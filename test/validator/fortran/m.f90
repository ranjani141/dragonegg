MODULE m
IMPLICIT NONE
    REAL, ALLOCATABLE :: &
        g_arr(:,:)

CONTAINS
    SUBROUTINE f()
        INTEGER :: &
            i, j

        REAL :: &
            coeff

        DO i=1, 3
           DO j=1,3
              g_arr(i, j) = 2
           END DO
        END DO
    END SUBROUTINE f
END MODULE m
