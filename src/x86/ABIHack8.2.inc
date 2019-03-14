
#define MAX_CLASSES 8

/* Return the "natural" mode for TYPE.  In most cases, this is just TYPE_MODE.
   But in the case of vector types, it is some vector mode.

   When we have only some of our vector isa extensions enabled, then there
   are some modes for which vector_mode_supported_p is false.  For these
   modes, the generic vector support in gcc will choose some non-vector mode
   in order to implement the type.  By computing the natural mode, we'll
   select the proper ABI location for the operand and not depend on whatever
   the middle-end decides to do with these vector types.

   The midde-end can't deal with the vector types > 16 bytes.  In this
   case, we return the original mode and warn ABI change if CUM isn't
   NULL. 

   If INT_RETURN is true, warn ABI change if the vector mode isn't
   available for function return value.  */

static machine_mode
type_natural_mode (const_tree type, const CUMULATIVE_ARGS *cum,
		   bool in_return = false)
{
  machine_mode mode = TYPE_MODE (type);

  if (TREE_CODE (type) == VECTOR_TYPE && !VECTOR_MODE_P (mode))
    {
      HOST_WIDE_INT size = int_size_in_bytes (type);
      if ((size == 8 || size == 16 || size == 32 || size == 64)
	  /* ??? Generic code allows us to create width 1 vectors.  Ignore.  */
	  && TYPE_VECTOR_SUBPARTS (type) > 1)
	{
	  machine_mode innermode = TYPE_MODE (TREE_TYPE (type));

	  /* There are no XFmode vector modes.  */
	  if (innermode == XFmode)
	    return mode;

	  if (TREE_CODE (TREE_TYPE (type)) == REAL_TYPE)
	    mode = MIN_MODE_VECTOR_FLOAT;
	  else
	    mode = MIN_MODE_VECTOR_INT;

	  /* Get the mode which has this inner mode and number of units.  */
	  FOR_EACH_MODE_FROM (mode, mode)
	    if (GET_MODE_NUNITS (mode) == TYPE_VECTOR_SUBPARTS (type)
		&& GET_MODE_INNER (mode) == innermode)
	      {
		if (size == 64 && !TARGET_AVX512F && !TARGET_IAMCU)
		  {
		    static bool warnedavx512f;
		    static bool warnedavx512f_ret;

		    if (cum && cum->warn_avx512f && !warnedavx512f)
		      {
			if (warning (OPT_Wpsabi, "AVX512F vector argument "
				     "without AVX512F enabled changes the ABI"))
			  warnedavx512f = true;
		      }
		    else if (in_return && !warnedavx512f_ret)
		      {
			if (warning (OPT_Wpsabi, "AVX512F vector return "
				     "without AVX512F enabled changes the ABI"))
			  warnedavx512f_ret = true;
		      }

		    return TYPE_MODE (type);
		  }
		else if (size == 32 && !TARGET_AVX && !TARGET_IAMCU)
		  {
		    static bool warnedavx;
		    static bool warnedavx_ret;

		    if (cum && cum->warn_avx && !warnedavx)
		      {
			if (warning (OPT_Wpsabi, "AVX vector argument "
				     "without AVX enabled changes the ABI"))
			  warnedavx = true;
		      }
		    else if (in_return && !warnedavx_ret)
		      {
			if (warning (OPT_Wpsabi, "AVX vector return "
				     "without AVX enabled changes the ABI"))
			  warnedavx_ret = true;
		      }

		    return TYPE_MODE (type);
		  }
		else if (((size == 8 && TARGET_64BIT) || size == 16)
			 && !TARGET_SSE
			 && !TARGET_IAMCU)
		  {
		    static bool warnedsse;
		    static bool warnedsse_ret;

		    if (cum && cum->warn_sse && !warnedsse)
		      {
			if (warning (OPT_Wpsabi, "SSE vector argument "
				     "without SSE enabled changes the ABI"))
			  warnedsse = true;
		      }
		    else if (!TARGET_64BIT && in_return && !warnedsse_ret)
		      {
			if (warning (OPT_Wpsabi, "SSE vector return "
				     "without SSE enabled changes the ABI"))
			  warnedsse_ret = true;
		      }
		  }
		else if ((size == 8 && !TARGET_64BIT)
			 && (!cfun
			     || cfun->machine->func_type == TYPE_NORMAL)
			 && !TARGET_MMX
			 && !TARGET_IAMCU)
		  {
		    static bool warnedmmx;
		    static bool warnedmmx_ret;

		    if (cum && cum->warn_mmx && !warnedmmx)
		      {
			if (warning (OPT_Wpsabi, "MMX vector argument "
				     "without MMX enabled changes the ABI"))
			  warnedmmx = true;
		      }
		    else if (in_return && !warnedmmx_ret)
		      {
			if (warning (OPT_Wpsabi, "MMX vector return "
				     "without MMX enabled changes the ABI"))
			  warnedmmx_ret = true;
		      }
		  }
		return mode;
	      }

	  gcc_unreachable ();
	}
    }

  return mode;
}

// /* We want to pass a value in REGNO whose "natural" mode is MODE.  However,
//    this may not agree with the mode that the type system has chosen for the
//    register, which is ORIG_MODE.  If ORIG_MODE is not BLKmode, then we can
//    go ahead and use it.  Otherwise we have to build a PARALLEL instead.  */

// static rtx
// gen_reg_or_parallel (machine_mode mode, machine_mode orig_mode,
// 		     unsigned int regno)
// {
//   rtx tmp;

//   if (orig_mode != BLKmode)
//     tmp = gen_rtx_REG (orig_mode, regno);
//   else
//     {
//       tmp = gen_rtx_REG (mode, regno);
//       tmp = gen_rtx_EXPR_LIST (VOIDmode, tmp, const0_rtx);
//       tmp = gen_rtx_PARALLEL (orig_mode, gen_rtvec (1, tmp));
//     }

//   return tmp;
// }


/* x86-64 register passing implementation.  See x86-64 ABI for details.  Goal
   of this code is to classify each 8bytes of incoming argument by the register
   class and assign registers accordingly.  */

/* Return the union class of CLASS1 and CLASS2.
   See the x86-64 PS ABI for details.  */

static enum x86_64_reg_class
merge_classes (enum x86_64_reg_class class1, enum x86_64_reg_class class2)
{
  /* Rule #1: If both classes are equal, this is the resulting class.  */
  if (class1 == class2)
    return class1;

  /* Rule #2: If one of the classes is NO_CLASS, the resulting class is
     the other class.  */
  if (class1 == X86_64_NO_CLASS)
    return class2;
  if (class2 == X86_64_NO_CLASS)
    return class1;

  /* Rule #3: If one of the classes is MEMORY, the result is MEMORY.  */
  if (class1 == X86_64_MEMORY_CLASS || class2 == X86_64_MEMORY_CLASS)
    return X86_64_MEMORY_CLASS;

  /* Rule #4: If one of the classes is INTEGER, the result is INTEGER.  */
  if ((class1 == X86_64_INTEGERSI_CLASS && class2 == X86_64_SSESF_CLASS)
      || (class2 == X86_64_INTEGERSI_CLASS && class1 == X86_64_SSESF_CLASS))
    return X86_64_INTEGERSI_CLASS;
  if (class1 == X86_64_INTEGER_CLASS || class1 == X86_64_INTEGERSI_CLASS
      || class2 == X86_64_INTEGER_CLASS || class2 == X86_64_INTEGERSI_CLASS)
    return X86_64_INTEGER_CLASS;

  /* Rule #5: If one of the classes is X87, X87UP, or COMPLEX_X87 class,
     MEMORY is used.  */
  if (class1 == X86_64_X87_CLASS
      || class1 == X86_64_X87UP_CLASS
      || class1 == X86_64_COMPLEX_X87_CLASS
      || class2 == X86_64_X87_CLASS
      || class2 == X86_64_X87UP_CLASS
      || class2 == X86_64_COMPLEX_X87_CLASS)
    return X86_64_MEMORY_CLASS;

  /* Rule #6: Otherwise class SSE is used.  */
  return X86_64_SSE_CLASS;
}

/* Classify the argument of type TYPE and mode MODE.
   CLASSES will be filled by the register class used to pass each word
   of the operand.  The number of words is returned.  In case the parameter
   should be passed in memory, 0 is returned. As a special case for zero
   sized containers, classes[0] will be NO_CLASS and 1 is returned.

   BIT_OFFSET is used internally for handling records and specifies offset
   of the offset in bits modulo 512 to avoid overflow cases.

   See the x86-64 PS ABI for details.
*/

static int
classify_argument (machine_mode mode, const_tree type,
		   enum x86_64_reg_class classes[MAX_CLASSES], int bit_offset)
{
  HOST_WIDE_INT bytes =
    (mode == BLKmode) ? int_size_in_bytes (type) : (int) GET_MODE_SIZE (mode);
  int words = CEIL (bytes + (bit_offset % 64) / 8, UNITS_PER_WORD);

  /* Variable sized entities are always passed/returned in memory.  */
  if (bytes < 0)
    return 0;

  if (mode != VOIDmode
      && targetm.calls.must_pass_in_stack (mode, type))
    return 0;

  if (type && AGGREGATE_TYPE_P (type))
    {
      int i;
      tree field;
      enum x86_64_reg_class subclasses[MAX_CLASSES];

      /* On x86-64 we pass structures larger than 64 bytes on the stack.  */
      if (bytes > 64)
	return 0;

      for (i = 0; i < words; i++)
	classes[i] = X86_64_NO_CLASS;

      /* Zero sized arrays or structures are NO_CLASS.  We return 0 to
	 signalize memory class, so handle it as special case.  */
      if (!words)
	{
	  classes[0] = X86_64_NO_CLASS;
	  return 1;
	}

      /* Classify each field of record and merge classes.  */
      switch (TREE_CODE (type))
	{
	case RECORD_TYPE:
	  /* And now merge the fields of structure.  */
	  for (field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
	    {
	      if (TREE_CODE (field) == FIELD_DECL)
		{
		  int num;

		  if (TREE_TYPE (field) == error_mark_node)
		    continue;

		  /* Bitfields are always classified as integer.  Handle them
		     early, since later code would consider them to be
		     misaligned integers.  */
		  if (DECL_BIT_FIELD (field))
		    {
		      for (i = (int_bit_position (field)
				+ (bit_offset % 64)) / 8 / 8;
			   i < ((int_bit_position (field) + (bit_offset % 64))
			        + tree_to_shwi (DECL_SIZE (field))
				+ 63) / 8 / 8; i++)
			classes[i] =
			  merge_classes (X86_64_INTEGER_CLASS,
					 classes[i]);
		    }
		  else
		    {
		      int pos;

		      type = TREE_TYPE (field);

		      /* Flexible array member is ignored.  */
		      if (TYPE_MODE (type) == BLKmode
			  && TREE_CODE (type) == ARRAY_TYPE
			  && TYPE_SIZE (type) == NULL_TREE
			  && TYPE_DOMAIN (type) != NULL_TREE
			  && (TYPE_MAX_VALUE (TYPE_DOMAIN (type))
			      == NULL_TREE))
			{
			  static bool warned;

			  if (!warned && warn_psabi)
			    {
			      warned = true;
			      inform (input_location,
				      "the ABI of passing struct with"
				      " a flexible array member has"
				      " changed in GCC 4.4");
			    }
			  continue;
			}
		      num = classify_argument (TYPE_MODE (type), type,
					       subclasses,
					       (int_bit_position (field)
						+ bit_offset) % 512);
		      if (!num)
			return 0;
		      pos = (int_bit_position (field)
			     + (bit_offset % 64)) / 8 / 8;
		      for (i = 0; i < num && (i + pos) < words; i++)
			classes[i + pos] =
			  merge_classes (subclasses[i], classes[i + pos]);
		    }
		}
	    }
	  break;

	case ARRAY_TYPE:
	  /* Arrays are handled as small records.  */
	  {
	    int num;
	    num = classify_argument (TYPE_MODE (TREE_TYPE (type)),
				     TREE_TYPE (type), subclasses, bit_offset);
	    if (!num)
	      return 0;

	    /* The partial classes are now full classes.  */
	    if (subclasses[0] == X86_64_SSESF_CLASS && bytes != 4)
	      subclasses[0] = X86_64_SSE_CLASS;
	    if (subclasses[0] == X86_64_INTEGERSI_CLASS
		&& !((bit_offset % 64) == 0 && bytes == 4))
	      subclasses[0] = X86_64_INTEGER_CLASS;

	    for (i = 0; i < words; i++)
	      classes[i] = subclasses[i % num];

	    break;
	  }
	case UNION_TYPE:
	case QUAL_UNION_TYPE:
	  /* Unions are similar to RECORD_TYPE but offset is always 0.
	     */
	  for (field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
	    {
	      if (TREE_CODE (field) == FIELD_DECL)
		{
		  int num;

		  if (TREE_TYPE (field) == error_mark_node)
		    continue;

		  num = classify_argument (TYPE_MODE (TREE_TYPE (field)),
					   TREE_TYPE (field), subclasses,
					   bit_offset);
		  if (!num)
		    return 0;
		  for (i = 0; i < num && i < words; i++)
		    classes[i] = merge_classes (subclasses[i], classes[i]);
		}
	    }
	  break;

	default:
	  gcc_unreachable ();
	}

      if (words > 2)
	{
	  /* When size > 16 bytes, if the first one isn't
	     X86_64_SSE_CLASS or any other ones aren't
	     X86_64_SSEUP_CLASS, everything should be passed in
	     memory.  */
	  if (classes[0] != X86_64_SSE_CLASS)
	      return 0;

	  for (i = 1; i < words; i++)
	    if (classes[i] != X86_64_SSEUP_CLASS)
	      return 0;
	}

      /* Final merger cleanup.  */
      for (i = 0; i < words; i++)
	{
	  /* If one class is MEMORY, everything should be passed in
	     memory.  */
	  if (classes[i] == X86_64_MEMORY_CLASS)
	    return 0;

	  /* The X86_64_SSEUP_CLASS should be always preceded by
	     X86_64_SSE_CLASS or X86_64_SSEUP_CLASS.  */
	  if (classes[i] == X86_64_SSEUP_CLASS
	      && classes[i - 1] != X86_64_SSE_CLASS
	      && classes[i - 1] != X86_64_SSEUP_CLASS)
	    {
	      /* The first one should never be X86_64_SSEUP_CLASS.  */
	      gcc_assert (i != 0);
	      classes[i] = X86_64_SSE_CLASS;
	    }

	  /*  If X86_64_X87UP_CLASS isn't preceded by X86_64_X87_CLASS,
	       everything should be passed in memory.  */
	  if (classes[i] == X86_64_X87UP_CLASS
	      && (classes[i - 1] != X86_64_X87_CLASS))
	    {
	      static bool warned;

	      /* The first one should never be X86_64_X87UP_CLASS.  */
	      gcc_assert (i != 0);
	      if (!warned && warn_psabi)
		{
		  warned = true;
		  inform (input_location,
			  "the ABI of passing union with long double"
			  " has changed in GCC 4.4");
		}
	      return 0;
	    }
	}
      return words;
    }

  /* Compute alignment needed.  We align all types to natural boundaries with
     exception of XFmode that is aligned to 64bits.  */
  if (mode != VOIDmode && mode != BLKmode)
    {
      int mode_alignment = GET_MODE_BITSIZE (mode);

      if (mode == XFmode)
	mode_alignment = 128;
      else if (mode == XCmode)
	mode_alignment = 256;
      if (COMPLEX_MODE_P (mode))
	mode_alignment /= 2;
      /* Misaligned fields are always returned in memory.  */
      if (bit_offset % mode_alignment)
	return 0;
    }

  /* for V1xx modes, just use the base mode */
  if (VECTOR_MODE_P (mode) && mode != V1DImode && mode != V1TImode
      && GET_MODE_UNIT_SIZE (mode) == bytes)
    mode = GET_MODE_INNER (mode);

  /* Classification of atomic types.  */
  switch (mode)
    {
    case E_SDmode:
    case E_DDmode:
      classes[0] = X86_64_SSE_CLASS;
      return 1;
    case E_TDmode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      return 2;
    case E_DImode:
    case E_SImode:
    case E_HImode:
    case E_QImode:
    case E_CSImode:
    case E_CHImode:
    case E_CQImode:
      {
	int size = bit_offset + (int) GET_MODE_BITSIZE (mode);

	/* Analyze last 128 bits only.  */
	size = (size - 1) & 0x7f;

	if (size < 32)
	  {
	    classes[0] = X86_64_INTEGERSI_CLASS;
	    return 1;
	  }
	else if (size < 64)
	  {
	    classes[0] = X86_64_INTEGER_CLASS;
	    return 1;
	  }
	else if (size < 64+32)
	  {
	    classes[0] = X86_64_INTEGER_CLASS;
	    classes[1] = X86_64_INTEGERSI_CLASS;
	    return 2;
	  }
	else if (size < 64+64)
	  {
	    classes[0] = classes[1] = X86_64_INTEGER_CLASS;
	    return 2;
	  }
	else
	  gcc_unreachable ();
      }
    case E_CDImode:
    case E_TImode:
      classes[0] = classes[1] = X86_64_INTEGER_CLASS;
      return 2;
    case E_COImode:
    case E_OImode:
      /* OImode shouldn't be used directly.  */
      gcc_unreachable ();
    case E_CTImode:
      return 0;
    case E_SFmode:
      if (!(bit_offset % 64))
	classes[0] = X86_64_SSESF_CLASS;
      else
	classes[0] = X86_64_SSE_CLASS;
      return 1;
    case E_DFmode:
      classes[0] = X86_64_SSEDF_CLASS;
      return 1;
    case E_XFmode:
      classes[0] = X86_64_X87_CLASS;
      classes[1] = X86_64_X87UP_CLASS;
      return 2;
    case E_TFmode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      return 2;
    case E_SCmode:
      classes[0] = X86_64_SSE_CLASS;
      if (!(bit_offset % 64))
	return 1;
      else
	{
	  static bool warned;

	  if (!warned && warn_psabi)
	    {
	      warned = true;
	      inform (input_location,
		      "the ABI of passing structure with complex float"
		      " member has changed in GCC 4.4");
	    }
	  classes[1] = X86_64_SSESF_CLASS;
	  return 2;
	}
    case E_DCmode:
      classes[0] = X86_64_SSEDF_CLASS;
      classes[1] = X86_64_SSEDF_CLASS;
      return 2;
    case E_XCmode:
      classes[0] = X86_64_COMPLEX_X87_CLASS;
      return 1;
    case E_TCmode:
      /* This modes is larger than 16 bytes.  */
      return 0;
    case E_V8SFmode:
    case E_V8SImode:
    case E_V32QImode:
    case E_V16HImode:
    case E_V4DFmode:
    case E_V4DImode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      classes[2] = X86_64_SSEUP_CLASS;
      classes[3] = X86_64_SSEUP_CLASS;
      return 4;
    case E_V8DFmode:
    case E_V16SFmode:
    case E_V8DImode:
    case E_V16SImode:
    case E_V32HImode:
    case E_V64QImode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      classes[2] = X86_64_SSEUP_CLASS;
      classes[3] = X86_64_SSEUP_CLASS;
      classes[4] = X86_64_SSEUP_CLASS;
      classes[5] = X86_64_SSEUP_CLASS;
      classes[6] = X86_64_SSEUP_CLASS;
      classes[7] = X86_64_SSEUP_CLASS;
      return 8;
    case E_V4SFmode:
    case E_V4SImode:
    case E_V16QImode:
    case E_V8HImode:
    case E_V2DFmode:
    case E_V2DImode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      return 2;
    case E_V1TImode:
    case E_V1DImode:
    case E_V2SFmode:
    case E_V2SImode:
    case E_V4HImode:
    case E_V8QImode:
      classes[0] = X86_64_SSE_CLASS;
      return 1;
    case E_BLKmode:
    case E_VOIDmode:
      return 0;
    default:
      gcc_assert (VECTOR_MODE_P (mode));

      if (bytes > 16)
	return 0;

      gcc_assert (GET_MODE_CLASS (GET_MODE_INNER (mode)) == MODE_INT);

      if (bit_offset + GET_MODE_BITSIZE (mode) <= 32)
	classes[0] = X86_64_INTEGERSI_CLASS;
      else
	classes[0] = X86_64_INTEGER_CLASS;
      classes[1] = X86_64_INTEGER_CLASS;
      return 1 + (bytes > 8);
    }
}

/* Examine the argument and return set number of register required in each
   class.  Return true iff parameter should be passed in memory.  */

static bool
examine_argument (machine_mode mode, const_tree type, int in_return,
		  int *int_nregs, int *sse_nregs)
{
  enum x86_64_reg_class regclass[MAX_CLASSES];
  int n = classify_argument (mode, type, regclass, 0);

  *int_nregs = 0;
  *sse_nregs = 0;

  if (!n)
    return true;
  for (n--; n >= 0; n--)
    switch (regclass[n])
      {
      case X86_64_INTEGER_CLASS:
      case X86_64_INTEGERSI_CLASS:
	(*int_nregs)++;
	break;
      case X86_64_SSE_CLASS:
      case X86_64_SSESF_CLASS:
      case X86_64_SSEDF_CLASS:
	(*sse_nregs)++;
	break;
      case X86_64_NO_CLASS:
      case X86_64_SSEUP_CLASS:
	break;
      case X86_64_X87_CLASS:
      case X86_64_X87UP_CLASS:
      case X86_64_COMPLEX_X87_CLASS:
	if (!in_return)
	  return true;
	break;
      case X86_64_MEMORY_CLASS:
	gcc_unreachable ();
      }

  return false;
}
