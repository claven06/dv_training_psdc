// file = 0; split type = patterns; threshold = 100000; total count = 0.
#include <stdio.h>
#include <stdlib.h>
#include <strings.h>
#include "rmapats.h"

void  schedNewEvent (struct dummyq_struct * I1462, EBLK  * I1457, U  I622);
void  schedNewEvent (struct dummyq_struct * I1462, EBLK  * I1457, U  I622)
{
    U  I1752;
    U  I1753;
    U  I1754;
    struct futq * I1755;
    struct dummyq_struct * pQ = I1462;
    I1752 = ((U )vcs_clocks) + I622;
    I1754 = I1752 & ((1 << fHashTableSize) - 1);
    I1457->I668 = (EBLK  *)(-1);
    I1457->I669 = I1752;
    if (0 && rmaProfEvtProp) {
        vcs_simpSetEBlkEvtID(I1457);
    }
    if (I1752 < (U )vcs_clocks) {
        I1753 = ((U  *)&vcs_clocks)[1];
        sched_millenium(pQ, I1457, I1753 + 1, I1752);
    }
    else if ((peblkFutQ1Head != ((void *)0)) && (I622 == 1)) {
        I1457->I671 = (struct eblk *)peblkFutQ1Tail;
        peblkFutQ1Tail->I668 = I1457;
        peblkFutQ1Tail = I1457;
    }
    else if ((I1755 = pQ->I1363[I1754].I691)) {
        I1457->I671 = (struct eblk *)I1755->I689;
        I1755->I689->I668 = (RP )I1457;
        I1755->I689 = (RmaEblk  *)I1457;
    }
    else {
        sched_hsopt(pQ, I1457, I1752);
    }
}
#ifdef __cplusplus
extern "C" {
#endif
void SinitHsimPats(void);
#ifdef __cplusplus
}
#endif
