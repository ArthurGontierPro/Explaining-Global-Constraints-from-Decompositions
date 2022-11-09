#include <chuffed/core/propagator.h>

template<int U = 0>
class Countx : public Propagator, public Checker {
public:
    vec<IntView<U> > x;
    int v;//value
    int n;//limit
    int nbvar;
    bool naive;

    int s;//number of variables with the value in their domain
    int f;//number of variables fixed to the value
    int littrue;
    int litfalse;

    int j;
    Clause *r;

    Countx(vec<IntView<U>> _x, int _v, int _n) : x(_x), v(_v), n(_n), nbvar(_x.size()) {
        // naive = true;
        // naive = false;
        naive = so.naive;
        // fprintf(stderr,"naive = %d\n", naive);
        priority = 2;
        s = nbvar;
        f = 0;
        littrue = 0;
        litfalse = 0;
        j = 1;
        r = NULL;

        for (int i = 0; i < x.size(); i++) x[i].attach(this, i, EVENT_C);
        //fprintf(stderr, "Countx::create()\n");
    }

    void wakeup(int i, int c) {
        if (x[i].isFixed() || !x[i].indomain(v)) {
            pushInQueue();
        }
    }

    int gettruelit() {
        if (littrue == 0 || !(x[littrue].isFixed() && x[littrue].indomain(v)))
            for (int i = 0; i < nbvar; i++)
                if (x[i].isFixed() && x[i].indomain(v))
                    littrue = i;
        return littrue;
    }

    int getfalselit() {
        if (litfalse == 0 || x[litfalse].indomain(v))
            for (int i = 0; i < nbvar; i++)
                if (!x[i].indomain(v))
                    litfalse = i;
        return litfalse;
    }

    bool propagate() {
        s = 0;
        f = 0;
        if (!filter(s, f)) {
            return false;
        }
        return true;
    }

    bool filter(int s, int f) {
        if (f <= n && s >= n) {
            return true;
        }
        if (s < n) {
            r = naive ? reason_all_state(getfalselit()) : reason_neq(nbvar - s);
            return x[getfalselit()].setVal(v, r);
        } else if (s == n) {
            return fixall();
        }
        if (f > n) {
            r = naive ? reason_all_state(gettruelit()) : reason_eq(f);
            return x[gettruelit()].remVal(v, r);
        } else if (f == n) {
            return remall();
        }
        return true;
    }

    Clause *reason_neq(int s) {
        r = Reason_new(s + 1);
        j = 1;
        for (int i = 0; i < nbvar; i++)
            if (!x[i].indomain(v))
                (*r)[j++] = x[i].getLit(v, 1);
        return r;
    }

    Clause *reason_eq(int s) {
        r = Reason_new(s + 1);
        j = 1;
        for (int i = 0; i < nbvar; i++)
            if (x[i].isFixed() && x[i].getVal() == v)
                (*r)[j++] = x[i].getLit(v, 0);
        return r;
    }

    Clause *reason_all_state(int pivot) {
        int c = 0;
        int trous = 0;
        for (int i = 0; i < nbvar; i++)
            if (i != pivot) {
                if (x[i].isFixed()) c++;
                else
                    for (int j = x[i].getMin(); j < x[i].getMax(); j++)
                        if (!x[i].indomain(j)) trous++;
            }
        r = Reason_new(1 + c + trous + 2 * (nbvar - c - 1));
        int k = 1;
        for (int i = 0; i < nbvar; i++)
            if (i != pivot) {
                if (x[i].isFixed())
                    (*r)[k++] = x[i].getValLit();
                else {
                    (*r)[k++] = x[i].getMinLit();
                    (*r)[k++] = x[i].getMaxLit();
                    for (int j = x[i].getMin(); j < x[i].getMax(); j++)
                        if (!x[i].indomain(j))
                            (*r)[k++] = x[i].getLit(j, 1);
                }
            }
        return r;
    }

    bool fixall() {
        r = naive ? NULL : reason_neq(nbvar - n);
        for (int i = 0; i < nbvar; i++)
            if (!x[i].isFixed() && x[i].indomain(v)) {
                if (naive) r = reason_all_state(i);//naive explanation
                if (!x[i].setVal(v, r)) return false;
            }
        return true;
    }

    bool remall() {
        Clause *r = naive ? NULL : reason_eq(n);
        for (int i = 0; i < nbvar; i++)
            if (!x[i].isFixed() && x[i].indomain(v)) {
                if (naive) r = reason_all_state(i);//naive explanation
                if (!x[i].remVal(v, r)) return false;
            }
        return true;
    }

    void clearPropState() {
        in_queue = false;
    }

    bool check() {
        s = 0;
        f = 0;
        for (int i = 0; i < nbvar; i++)
            if (x[i].indomain(v)) {
                s++;
                if (x[i].isFixed()) f++;
            }
        return f == n;
    }
};

template<int U = 0>
class Countxn : public Propagator, public Checker {
public:
    vec<IntView<U> > x;
    int v;//value
    IntView<U> n;//limit var
    int nbvar;
    bool naive;

    int s;//number of variables with the value in their domain
    int f;//number of variables fixed to the value
    int ns;//n upper bound
    int nf;//nlower bound

    int j;
    Clause *r;

    Countxn(vec<IntView<U>> _x, int _v, IntView<U> _n) : x(_x), v(_v), n(_n), nbvar(_x.size()) {
        // naive = true;
        // naive = false;
        naive = so.naive;
        priority = 2;
        r = NULL;
        j = 1;

        for (int i = 0; i < x.size(); i++) x[i].attach(this, i, EVENT_C);
        n.attach(this, nbvar + 1, EVENT_LU);
        //fprintf(stderr, "Countxn::create()\n");
    }

    void wakeup(int i, int c) {
        if (i == nbvar + 1)
            pushInQueue();
        else {
            if (x[i].isFixed() || !x[i].indomain(v)) {
                pushInQueue();
            }
        }
    }

    bool propagate() {
        s = 0;
        f = 0;
        for (int i = 0; i < nbvar; i++)
            if (x[i].indomain(v)) {
                s++;
                if (x[i].isFixed()) f++;
            }
        ns = n.getMax();
        nf = n.getMin();
        if (!filter(s, f, ns, nf)) {
            return false;
        }
        return true;
    }

    bool filter(int s, int f, int ns, int nf) {
        if (f == s && nf == ns && nf == f) return true;// tout vas bien
        if (f > nf) {// modif de la borne de n
            r = naive ? reason_all_state() : reason_eq(f);
            return n.setMin(f, r);
        }
        if (s < ns) {
            r = naive ? reason_all_state() : reason_neq(nbvar - s);
            return n.setMax(s, r);
        }
        // modif des x
        if (nf == ns) {
            if (f == ns) return remall(ns);
            if (s == nf) return fixall(nf);
        }
        return true;
    }

    Clause *reason_neq(int s) {
        r = Reason_new(s + 1);
        j = 1;
        for (int i = 0; i < nbvar; i++)
            if (!x[i].indomain(v))
                (*r)[j++] = x[i].getLit(v, 1);
        return r;
    }

    Clause *reason_eq(int s) {
        r = Reason_new(s + 1);
        j = 1;
        for (int i = 0; i < nbvar; i++)
            if (x[i].isFixed() && x[i].getVal() == v)
                (*r)[j++] = x[i].getLit(v, 0);
        return r;
    }

    Clause *reason_neq_nf(int s) {
        r = Reason_new(s + 2);
        (*r)[1] = n.getMinLit();
        j = 2;
        for (int i = 0; i < nbvar; i++)
            if (!x[i].indomain(v))
                (*r)[j++] = x[i].getLit(v, 1);
        return r;
    }

    Clause *reason_eq_ns(int s) {
        r = Reason_new(s + 2);
        (*r)[1] = n.getMaxLit();
        j = 2;
        for (int i = 0; i < nbvar; i++)
            if (x[i].isFixed() && x[i].getVal() == v)
                (*r)[j++] = x[i].getLit(v, 0);
        return r;
    }

    Clause *reason_all_state() {//n is the pivot
        int c = 0;
        int trous = 0;
        for (int i = 0; i < nbvar; i++)
            if (x[i].isFixed()) c++;
            else
                for (int j = x[i].getMin(); j < x[i].getMax(); j++)
                    if (!x[i].indomain(j)) trous++;
        r = Reason_new(1 + c + trous + 2 * (nbvar - c));
        int k = 1;
        for (int i = 0; i < nbvar; i++)
            if (x[i].isFixed())
                (*r)[k++] = x[i].getValLit();
            else {
                (*r)[k++] = x[i].getMinLit();
                (*r)[k++] = x[i].getMaxLit();
                for (int j = x[i].getMin(); j < x[i].getMax(); j++)
                    if (!x[i].indomain(j))
                        (*r)[k++] = x[i].getLit(j, 1);
            }
        return r;
    }

    Clause *reason_all_state(int pivot) {
        int c = 0;
        int trous = 0;
        for (int i = 0; i < nbvar; i++)
            if (i != pivot) {
                if (x[i].isFixed()) c++;
                else
                    for (int j = x[i].getMin(); j < x[i].getMax(); j++)
                        if (!x[i].indomain(j)) trous++;
            }
        Clause *r = Reason_new(1 + 2 + c + trous + 2 * (nbvar - c - 1));
        (*r)[1] = n.getMinLit();
        (*r)[2] = n.getMaxLit();
        int k = 3;
        for (int i = 0; i < nbvar; i++)
            if (i != pivot) {
                if (x[i].isFixed())
                    (*r)[k++] = x[i].getValLit();
                else {
                    (*r)[k++] = x[i].getMinLit();
                    (*r)[k++] = x[i].getMaxLit();
                    for (int j = x[i].getMin(); j < x[i].getMax(); j++)
                        if (!x[i].indomain(j))
                            (*r)[k++] = x[i].getLit(j, 1);
                }
            }
        return r;
    }

    bool fixall(int n) {
        r = naive ? NULL : reason_neq_nf(nbvar - n);
        for (int i = 0; i < nbvar; i++)
            if (!x[i].isFixed() && x[i].indomain(v)) {
                if (naive) r = reason_all_state(i);
                if (!x[i].setVal(v, r)) return false;
            }
        return true;
    }

    bool remall(int n) {
        r = naive ? NULL : reason_eq_ns(n);
        for (int i = 0; i < nbvar; i++)
            if (!x[i].isFixed() && x[i].indomain(v)) {
                if (naive) r = reason_all_state(i);
                if (!x[i].remVal(v, r)) return false;
            }
        return true;
    }

    void clearPropState() {
        in_queue = false;
    }

    bool check() {
        s = 0;
        f = 0;
        for (int i = 0; i < nbvar; i++)
            if (x[i].indomain(v)) {
                s++;
                if (x[i].isFixed()) f++;
            }
        ns = n.getMax();
        nf = n.getMin();
        return f == s && nf == ns && nf == f;
    }
};


void count(vec<IntVar *> &x, int v, int n) {
    int min = INT_MAX, max = INT_MIN;
    vec<IntView<> > u;
    for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i], 1, -min));
    new Countx<0>(u, v, n);
}

void count(vec<IntVar *> &x, int v, IntVar *n) {
    int min = INT_MAX, max = INT_MIN;
    vec<IntView<> > u;
    for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i], 1, -min));
    new Countxn<0>(u, v, IntView<>(n));
}

/*
make
cmake ..
cmake --build . --target fzn-chuffed

cmake --build . --target examples 
./queens 10


EVENT_C = 1,		// Any change in the domain of the variable
EVENT_L = 2,		// Lower bound change of the variable
EVENT_U = 4,		// Upper bound change of the variable
EVENT_F = 8,		// When the variable is fixed
EVENT_LU = 6,		// Lower and upper bound change of the variable
EVENT_LF = 10,		// Lower bound change and fixation of the variable
EVENT_UF = 12		// Upper bound change and fixation of the variable

*/


