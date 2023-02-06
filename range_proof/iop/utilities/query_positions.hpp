/**@file
 *****************************************************************************
 Utility methods for IOP query position handles
 *****************************************************************************
 * @author     This file is part of Aurora in libiop
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/
#ifndef range_proof_IOP_UTILITIES_QUERY_POSITIONS_HPP_
#define range_proof_IOP_UTILITIES_QUERY_POSITIONS_HPP_

#include <vector>

#include "range_proof/algebra/field_subset/field_subset.hpp"
#include "range_proof/iop/iop.hpp"

namespace range_proof {

/** TODO: Come up with better name
 *
 */
template<typename FieldT>
std::vector<query_position_handle> query_position_to_queries_for_entire_coset(
    iop_protocol<FieldT> &IOP,
    const query_position_handle &initial_query,
    const field_subset<FieldT> &domain,
    const size_t coset_size);

} // namespace range_proof

#include "range_proof/iop/utilities/query_positions.tcc"

#endif // range_proof_IOP_UTILITIES_QUERY_POSITIONS_HPP_
