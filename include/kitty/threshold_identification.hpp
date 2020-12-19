/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "isop.hpp"

namespace kitty {

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
    template<typename TT, typename = std::enable_if_t <is_complete_truth_table<TT>::value>>
    bool is_threshold(const TT &tt, std::vector <int64_t> *plf = nullptr) {
        int n = tt.num_vars();
        std::vector <int64_t> linear_form(n+1);
        TT fstar_tt = tt;
        std::vector<bool> was_flipped(n, false);
        bool debug = false;

        // UNATENESS
        for (int i = 0; i < n; i++) {
            auto negative_cofactor = cofactor0(fstar_tt, i);
            auto positive_cofactor = cofactor1(fstar_tt, i);
            bool is_positive_unate = true;
            bool is_negative_unate = true;
            int cofactor_size = positive_cofactor.num_bits();
            //assert(n == cofactor_size); no need to have i!= j
            for (int j = 0; j < cofactor_size; j++) {
                if (get_bit(positive_cofactor, j) > get_bit(negative_cofactor, j)) { //cannot be negatively unate
                    is_negative_unate = false;
                } else if (get_bit(negative_cofactor, j) > get_bit(positive_cofactor, j)) {
                    is_positive_unate = false;
                } // if equal, could be any of it
            }
            if (is_negative_unate && !is_positive_unate) {// need to flip the variable
                was_flipped[i] = true;
                flip_inplace(fstar_tt, i);
            } else if (!is_positive_unate) { //function is binate, not TF
                return false;
            } //function is positively unate in the variable, nothing to do
        }
        // f is now positively unate (or we already went out of the function)

        // Build the ilp
        //make the empty ilp thing
        lprec *ilp; // code from lp_solve documentation
        ilp = make_lp(0, n + 1); // No constraints yet, n vars + T
        if (ilp == NULL) {
            fprintf(stderr, "Unable to create new LP model\n");
            return false;
        }
        // minimisation
        set_minim( ilp );
        //set the minimisation function
        std::vector <REAL> min_fun(n + 2, 1.0); //n+1 column so size n+2 (index 0 is ignored)
        // sum of all weights and T
        set_obj_fn(ilp, min_fun.data());

        // add the constraints
        std::vector <REAL> constraint(n + 2, 0.0); //n+1 column so size n+2 (index 0 is ignored)
        set_verbose(ilp, IMPORTANT);

        // list of on-set cubes
        if (debug) {
            std::cout << "onset" << std::endl;
        }
        for (auto &on_set_cube : isop(fstar_tt)) {
            // variables
            std::vector <REAL> constraint(n + 2, 0.0); //reset all the constraints to 0
            for (int i = 0; i < n; i++) {
                if (on_set_cube.get_mask(i) && on_set_cube.get_bit(i)) { // variable in cube and is positive
                    constraint[i + 1] = 1.0;
                }
            }
            // var_const >= T -> var_const - T >= 0
            constraint[n + 1] = -1.0;
            if (debug) {
                for (int i = 0; i< n+2; i++) {
                    std::cout << constraint[i] << " " ;
                }
                std::cout << ">= 0" << std::endl;
            }
            add_constraint(ilp, constraint.data(), GE, 0.0);
        }

        //list of off-set cubes
        if (debug) {
            std::cout << "offset" << std::endl;
        }
        for (auto &off_set_cube : isop(~fstar_tt)) {
            //
            std::vector <REAL> constraint(n + 2, 0.0); //reset all the constraints to 0
            for (int i = 0; i < n; i++) {
                if ((off_set_cube.get_mask(i) && off_set_cube.get_bit(i)) || !off_set_cube.get_mask(i)) { // variable in cube and is positive or not in cube
                    constraint[i + 1] = 1.0;
                }
            }
            // var_const <= T -1 -> var_const - T <= -1
            constraint[n + 1] = -1.0;
            if (debug) {
                for (int i = 0; i< n+2; i++) {
                    std::cout << constraint[i] << " " ;
                }
                std::cout << "<= -1" << std::endl;
            }
            add_constraint(ilp, constraint.data(), LE, -1.0);
        }

        // All weights are positive
        for (int i = 1; i < n + 2; i++) {
            std::vector <REAL> constraint(n + 2, 0.0); //reset all the constraints to 0
            constraint[i] = 1.0;
            if (debug) {
                for (int i = 0; i< n+2; i++) {
                    std::cout << constraint[i] << " " ;
                }
                std::cout << ">= 0"  << std::endl;
            }
            add_constraint(ilp, constraint.data(), GE, 0.0);
        }

        // ILP, all variables are integers
        for (int i = 1; i < n + 2; i++) {
            set_int(ilp, i, TRUE);
        }

        set_add_rowmode(ilp, FALSE);

        // SOLVE THE ILP
        int ret = solve(ilp);
        if (ret != 0 && ret != 1) { //solve returns 0 if an optimal solution was found and 1 if suboptimal
            return false;
        }

        std::vector<REAL> result(n+1);
        get_variables(ilp, result.data());
        if (ret) {
            fprintf(stderr, "Error retrieving solution\n");
            return false;
        }

        for (int i = 0; i < n + 1; i++) {
            linear_form[i] = (int) result[i];
            if (debug) {
                std::cout << result[i] << " " << linear_form[i] << std::endl;
            }
        }
        //lp cleanup
        delete_lp(ilp);

        // turn f* into f
        for (int i = 0; i < n; i++) {
            // for each variable that was flipped, get the weight negative and substract it from T
            if (was_flipped[i]) {
                linear_form[n] -= linear_form[i];
                linear_form[i] *= -1;
            }
            if (debug) {
                std::cout << linear_form[i] << std::endl;
            }
        }
        if (debug) {
            std::cout << "T is " << linear_form[n+1] << std::endl;
        }

        /* if tt is TF: */
        /* push the weight and threshold values into `linear_form` */
        if (plf) {
            *plf = linear_form;
        }

        return true;
    }


} /* namespace kitty */
