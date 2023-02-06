/**@file
 *****************************************************************************
 Superclass for "simple" LDTs (any of these can be used as a component of
 multi_ldt).
 *****************************************************************************
 * @author     This file is part of Aurora in libiop
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/
#ifndef LIBIOP_PROTOCOLS_LDT_MULTI_LDT_BASE_HPP_
#define LIBIOP_PROTOCOLS_LDT_MULTI_LDT_BASE_HPP_

#include "range_proof/algebra/field_subset/subspace.hpp"
#include "range_proof/iop/iop.hpp"

namespace range_proof {

template<typename FieldT>
class multi_LDT_parameter_base {
    public:
    virtual ~multi_LDT_parameter_base() {};
};

template<typename FieldT>
class multi_LDT_base {
protected:
    iop_protocol<FieldT> &IOP_;
    domain_handle codeword_domain_handle_;
    std::vector<oracle_handle_ptr> poly_handles_;
public:
    /* Initialization and registration */
    multi_LDT_base(iop_protocol<FieldT> &IOP,
                   multi_LDT_parameter_base<FieldT> &params,
                   const domain_handle &codeword_domain_handle,
                   const std::vector<oracle_handle_ptr> &poly_handles) :
        IOP_(IOP),
        codeword_domain_handle_(codeword_domain_handle),
        poly_handles_(poly_handles)
    { };

    void register_interactions();
    void register_queries();

    /* Verification */
    bool verifier_predicate();

    virtual ~multi_LDT_base() {};
};

} // namespace libiop

#endif
