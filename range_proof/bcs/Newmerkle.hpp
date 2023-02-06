#ifndef __merkle_tree
#define __merkle_tree
#include "range_proof/bcs/hash_packing.hpp"
#include <vector>

namespace range_proof{
struct merkleTreeParameter{
    std::vector<uint8_t> commit_root;
    std::vector<std::pair<std::size_t,std::vector<uint8_t>>> auxiliary_hash;
    std::vector<std::pair<std::size_t,std::vector<uint8_t>>> public_hash;
    std::size_t path_lenth;
};

template<typename FieldT>
class merkle{
protected:
    std::shared_ptr<blake3HASH<FieldT>> HashFunction;
    std::size_t leavesNum_;
public:
    merkle(const std::size_t leavesNum,
           const std::vector<std::size_t> &queries,
           const bool type);
    void create_tree_of_matrix(const std::vector<std::vector<FieldT>>& matrix_data);
    void create_tree_of_vec(const std::vector<FieldT> &vec_data);
    bool check_merkle_tree_correct(const std::vector<std::vector<uint8_t>>& allNodes);
    std::vector<std::pair<std::size_t,std::vector<uint8_t>>> find_merkle_path(const std::vector<std::vector<uint8_t>> &data);
    std::vector<std::pair<std::size_t,std::vector<uint8_t>>> find_merkle_path_by_index(const std::vector<std::vector<uint8_t>> &data,const std::vector<std::size_t>&query_index);
    std::vector<std::size_t> find_merkle_path_only_index(std::size_t allNodeSize);
    std::vector<std::size_t> get_queries(std::size_t query_num,std::size_t domain_size);
    std::vector<std::pair<std::size_t,std::vector<uint8_t>>> get_public_hash_postion(const std::vector<std::vector<uint8_t>>& data);
    merkleTreeParameter create_merklePar_of_matrix(const std::vector<std::vector<FieldT>>& matrix_data);
    merkleTreeParameter create_merklePar_of_vec(const std::vector<FieldT>& vec_data);
    merkleTreeParameter create_merklePar_of_vec_by_index(const std::vector<FieldT>&vec_data,const std::vector<std::size_t>&auxiliary_pos);
    merkleTreeParameter create_merklePar_of_mat_by_index(const std::vector<std::vector<FieldT>>& matrix_data,const std::vector<std::size_t>&auxiliary_pos );
    bool verify_merkle_commit(const merkleTreeParameter& par);
    std::vector<std::vector<uint8_t>> allNodes_;
    const std::vector<std::size_t> queries_;
    std::vector<std::size_t> query_index_;
    bool type_;
};
}
#include "range_proof/bcs/Newmerkle.tcc"
#endif