#ifndef PROJECT_CONSTRAINT_H
#define PROJECT_CONSTRAINT_H

#include "InstructionUtils.h"
#include "z3++.h"

using namespace z3;

namespace DRCHECKER {

    // This class abstracts the path constraints posed to a certain variable, within one function. 
    class Constraint {
    public:

        Value *v = nullptr;
        Function *func = nullptr;

        context z3c;
        solver *z3s = nullptr;
        expr *zv = nullptr;

        std::map<BasicBlock*, expr*> cons;

        //All BBs in which the value constraints are unsatisfiable.
        std::set<BasicBlock*> deadBBs;

        Constraint(Value *v, Function *func) {
            this->v = v;
            this->func = func;
            //We need to map the llvm value to the z3 domain.
            //For now we simply create a z3 integer for all llvm vars.
            //TODO: consider different z3 counterparts for different llvm vars.
            this->zv = new expr(this->z3c);
            *(this->zv) = z3c.int_const("v");
            this->z3s = new solver(this->z3c);
        }

        ~Constraint() {
            //
        }

        bool satisfiable(expr *e) {
            if (!e) {
                return false;
            }
            this->z3s->reset();
            this->z3s->add(*e);
            //"sat", "unsat" or "unknown"
            switch (this->z3s->check()) {
            case unsat: return false;
            default: return true;
            }
            return false;
        }

        //Add a new constraint for the value in a certain BB, then returns whether for this BB the
        //value constraint can be satisfied.
        bool addConstraint(expr *con, BasicBlock *bb) {
            if (!con || !bb) {
                return true;
            }
            if (this->deadBBs.find(bb) != this->deadBBs.end()) {
                //Already dead..
                return false;
            }
            if (this->cons.find(bb) == this->cons.end()) {
                expr *e = new expr(this->z3c);
                *e = *con;
                this->cons[bb] = e;
            }else {
                //Combine the constraints w/ "and".
                *(this->cons[bb]) = (*(this->cons[bb]) && *con);
            }
            if (!this->satisfiable(this->cons[bb])) {
                //Simplify the constraint to "false".
                *(this->cons[bb]) = this->z3c.bool_val(false);
                this->deadBBs.insert(bb);
                return false;
            }
            return true;
        }

        //Add the constraint to all basic blocks in the host function.
        void addConstraint2AllBBs(expr *con) {
            if (!this->func || !con) {
                return;
            }
            for (BasicBlock &bb : *(this->func)) {
                this->addConstraint(con,&bb);
            }
            return;
        }

        void addConstraint2BBs(expr *con, std::set<BasicBlock*> &bbs) {
            if (!con || bbs.empty()) {
                return;
            }
            for (BasicBlock *bb : bbs) {
                this->addConstraint(con,bb);
            }
            return;
        }

        expr getEqvExpr(std::set<int64_t> &vs) {
            expr e = this->z3c.bool_val(false);
            if (!this->zv) {
                return e;
            }
            for (int64_t i : vs) {
                e = (e || (*(this->zv) == this->z3c.int_val(i)));
            }
            return e;
        }

    private:
        //
    };

} //namespace

#endif //PROJECT_CONSTRAINT_H
