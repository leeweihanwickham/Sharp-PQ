/**@file
 *****************************************************************************
 Classes for linearized polynomials over GF(2) extensions.
 *****************************************************************************
 * @author     This file is This file is part of Aurora in libiop
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/
#ifndef range_proof_ALGEBRA_POLYNOMIALS_LINEARIZED_POLYNOMIAL_HPP_
#define range_proof_ALGEBRA_POLYNOMIALS_LINEARIZED_POLYNOMIAL_HPP_

#include <cstddef>
#include <vector>

#include "range_proof/algebra/field_subset/field_subset.hpp"
#include "range_proof/algebra/field_subset/subspace.hpp"
#include "range_proof/algebra/field_subset/subgroup.hpp"
#include "range_proof/algebra/polynomials/polynomial.hpp"

namespace range_proof {

/* linearized_polynomial implements affine linearized polynomials, so
   coefficients_ list the constant term, term for x, x^2, x^4, and so
   on.

   The linearized components of these polynomials enjoy bilinear
   properties, but handling constant term requires extra care (see
   evaluations_over_subspace for example) */
template<typename FieldT>
class linearized_polynomial : public polynomial<FieldT> {
public:
    explicit linearized_polynomial();
    explicit linearized_polynomial(std::vector<FieldT> &&coefficients);

    FieldT constant_coefficient() const;

    FieldT evaluation_at_point(const FieldT &evalpoint) const;
    /** The linearized polynomials are only implemented for binary fields,
     *  so the field_subset must be an affine subspace */
    std::vector<FieldT> evaluations_over_field_subset(const field_subset<FieldT> &S) const;
    std::vector<FieldT> evaluations_over_subspace(const affine_subspace<FieldT> &S) const;

    void square();
    linearized_polynomial<FieldT> squared() const;

    polynomial<FieldT> expand_as_polynomial() const;

    std::size_t degree() const;

    linearized_polynomial<FieldT>& operator+=(const linearized_polynomial<FieldT> &other);
    linearized_polynomial<FieldT> operator+(const linearized_polynomial<FieldT> &other) const;

    linearized_polynomial<FieldT>& operator*=(const FieldT &el);
    linearized_polynomial<FieldT> operator*(const FieldT &el) const;
    polynomial<FieldT> operator*(const polynomial<FieldT> &p) const;

    bool operator==(const linearized_polynomial<FieldT> &other) const;
    bool operator!=(const linearized_polynomial<FieldT> &other) const;

    static linearized_polynomial<FieldT> random_linearized_polynomial(const size_t degree_exponent);
};

// Returns the quotient and remainder of P / Z
template<typename FieldT>
std::pair<polynomial<FieldT>,
          polynomial<FieldT> >
polynomial_over_linearized_polynomial(const polynomial<FieldT> &P,
                                      const linearized_polynomial<FieldT> &Z);

} // namespace range_proof

#include "range_proof/algebra/polynomials/linearized_polynomial.tcc"

#endif // range_proof_ALGEBRA_POLYNOMIALS_LINEARIZED_POLYNOMIAL_HPP_
