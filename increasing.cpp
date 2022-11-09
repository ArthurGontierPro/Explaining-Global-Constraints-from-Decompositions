#include <chuffed/core/propagator.h>

template <int U = 0>
class Increasing : public Propagator, public Checker {
public:
	vec<IntView<U> > x;
	int nbvar;
	bool naive;

	Clause* r;

	Increasing(vec<IntView<U>> _x) : x(_x), nbvar(_x.size()) {
		// naive = true;
		// naive = false;		
		naive = so.naive;
		// fprintf(stderr,"naive = %d\n", naive);
		priority = 2;
		r=NULL;
		//fprintf(stderr,"alo\n");
		if (nbvar < 2) fprintf(stderr,"ERROR increasing on less than 2 vars\n");

		for (int i = 0; i < x.size(); i++) x[i].attach(this, i, EVENT_LU);
        //fprintf(stderr, "Increasing::create()\n");
	}
	void wakeup(int i, int c) {
		pushInQueue();
	}
	bool propagate() {
		for (int i = 1; i < nbvar; i++) {
			if (x[nbvar-i-1].getMax() > x[nbvar-i].getMax()){
				r = Reason_new(2);
				(*r)[1] = x[nbvar-i].getMaxLit();
				if (naive) r = reason_all_state(i);
				if (!x[nbvar-i-1].setMax(x[nbvar-i].getMax(),r))
					return false;
			}
			if (x[i-1].getMin() > x[i].getMin()){
				r = Reason_new(2);
				(*r)[1] = x[i-1].getMinLit();
				if (naive) r = reason_all_state(i);
				if (!x[i].setMin(x[i-1].getMin(),r))
					return false;
			}
		}
		return true;
	}
	Clause* reason_all_state(int pivot){
		r = Reason_new(2*(nbvar-1)+1);
		for (int i = 0, j = 0; i < nbvar; i++){
		    if (i!=pivot){
		        (*r)[2*j+1] = x[i].getMinLit();
		        (*r)[2*j+2] = x[i].getMaxLit();
		        j++;
		    }
		}
		return r;
	}
	void clearPropState() {
		in_queue = false;
	}

	bool check() {
		for (int i = 1; i < nbvar; i++) {
			if (x[nbvar-i-1].getMax() > x[nbvar-i].getMax()){
				return false;
			}
			if (x[i-1].getMin() > x[i].getMin()){
				return false;
			}
		}
		return true;
	}
	int checkSatisfied() {
		if (check()) return 1;
		return 2;
	}
};


void increasing(vec<IntVar*>& x){
	int min = INT_MAX, max = INT_MIN;
	vec<IntView<> > u;
	for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i],1,-min));
	new Increasing<0>(u); 
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
