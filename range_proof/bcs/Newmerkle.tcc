#include "range_proof/bcs/hash_packing.hpp"
#include "Newmerkle.hpp"
#include <algorithm>
#include "hash_packing.hpp"

namespace range_proof{
template<typename FieldT>
merkle<FieldT>::merkle(const std::size_t leavesNum,
                       const std::vector<std::size_t> &queries,
                       const bool type):
    leavesNum_(leavesNum),
    queries_(queries),
    type_(type)
{
    assert((leavesNum_&(leavesNum_-1))==0);
}

// 对矩阵承诺
template<typename FieldT>
void merkle<FieldT>::create_tree_of_matrix(const std::vector<std::vector<FieldT>>& matrix_data) {
    // type: true则按列做哈希 false则按行做哈希 默认是按列
    // data：输入的矩阵 按行存储 先转为按列 即先算叶子节点
    // 返回整个默克尔树
    blake3HASH<FieldT> hashFunction;
    // 按列做哈希
    if(type_){
        allNodes_.clear();
        std::size_t leavesNum=matrix_data[0].size();
//    判断输入节点个数为2^dim-->即列的数目
        assert((leavesNum&(leavesNum-1))==0);
//    首先计算叶子节点的哈希 先转置
        std::vector<FieldT> slice(matrix_data.size(),FieldT::zero());
        for(std::size_t i=0;i<leavesNum;i++){
            for(std::size_t j = 0; j < matrix_data.size(); j++){
                slice[j]=matrix_data[j][i];
            }
            allNodes_.push_back(std::move(hashFunction.get_one_hash(slice)));
        }
//    计算剩余的节点
        std::vector<std::vector<uint8_t>> tempNodes=allNodes_;
        while(leavesNum>1){
            std::vector<std::vector<uint8_t>> parentNodes;
            parentNodes.clear();
            for(std::size_t i=0;i<leavesNum;i=i+2){
                assert(tempNodes.size()==leavesNum);
                parentNodes.emplace_back(std::move(hashFunction.two_to_one_hash(tempNodes[i],tempNodes[i+1])));
            }
            allNodes_.insert(allNodes_.begin(),parentNodes.begin(),parentNodes.end());
            tempNodes.clear();
            tempNodes.assign(parentNodes.begin(),parentNodes.end());
            leavesNum=leavesNum>>1;
        }
    } else{
        allNodes_.clear();
        std::size_t leavesNum=matrix_data.size();
        //    判断输入节点个数为2^dim-->即行的数目
        assert((leavesNum&(leavesNum-1))==0);
        //    首先计算叶子节点的哈希 不用转置
        for(std::size_t i=0;i<leavesNum;i++){
            allNodes_.push_back(std::move(hashFunction.get_one_hash(matrix_data[i])));
        }
        //    计算剩余的节点
        std::vector<std::vector<uint8_t>> tempNodes=allNodes_;
        while(leavesNum>1){
            std::vector<std::vector<uint8_t>> parentNodes;
            parentNodes.clear();
            for(std::size_t i=0;i<leavesNum;i=i+2){
                assert(tempNodes.size()==leavesNum);
                parentNodes.emplace_back(std::move(hashFunction.two_to_one_hash(tempNodes[i],tempNodes[i+1])));
            }
            allNodes_.insert(allNodes_.begin(),parentNodes.begin(),parentNodes.end());
            tempNodes.clear();
            tempNodes.assign(parentNodes.begin(),parentNodes.end());
            leavesNum=leavesNum>>1;
        }
    }
}

// 对向量承诺
template<typename FieldT>
void merkle<FieldT>::create_tree_of_vec(const std::vector<FieldT>& vec_data){
    blake3HASH<FieldT> hashFunction;
    allNodes_.clear();

    std::size_t leavesNum=vec_data.size();
//    判断输入节点个数为2^dim-->即向量元素的数目
    assert((leavesNum&(leavesNum-1))==0);
    allNodes_.resize(2*leavesNum-1);
//    首先计算叶子节点的哈希
    for(std::size_t i=0;i<leavesNum;i++){
        allNodes_[leavesNum-1+i]=std::move(hashFunction.get_element_hash(vec_data[i]));
    }
//    计算剩余的节点
    std::size_t parent_index=leavesNum-2;
    for(std::size_t i=2*leavesNum-2;i>1;i=i-2){
        allNodes_[parent_index]=std::move(hashFunction.two_to_one_hash(allNodes_[i-1],allNodes_[i]));
        parent_index--;
    }
    assert(parent_index==-1);
}
template<typename FieldT>
bool merkle<FieldT>::check_merkle_tree_correct(const std::vector<std::vector<uint8_t>>& allNodes) {
    std::size_t parent=0,it=1,next_it=2;
    blake3HASH<FieldT> hashFunction;
    std::size_t lenth=allNodes.size();
    assert(((lenth+1)&lenth)==0);
    while(next_it<lenth){
        if(allNodes[parent]!=hashFunction.two_to_one_hash(allNodes[it],allNodes[next_it])){
            std::cout<<"parent: "<<parent<<" ";
            for (size_t i = 0; i < BLAKE3_OUT_LEN; i++) {
                printf("%02x", allNodes[parent][i]);
            }
            std::cout<<" temp ";
            std::cout<<" child: "<<it<<" ";
            for (size_t i = 0; i < BLAKE3_OUT_LEN; i++) {
                printf("%02x", allNodes[it][i]);
            }
            std::cout<<" child: "<<next_it<<" ";
            for (size_t i = 0; i < BLAKE3_OUT_LEN; i++) {
                printf("%02x", allNodes[next_it][i]);
            }
            std::cout<<"\n";
            return false;
        }
        parent+=1;
        it+=2;
        next_it+=2;
    }
    return true;
}


template<typename FieldT>
std::vector<std::pair<std::size_t,std::vector<uint8_t>>> merkle<FieldT>::find_merkle_path(const std::vector<std::vector<uint8_t>> &data) {
//  认为positions已排好序 且符合merkle树的查询范围 即positions的范围在2^(k-1)~2^k-1 对应叶子节点的索引
//  返回默克尔树的路径 res.size就是要求的路径长度
//  data: create_tree里的返回值 allnode
    std::vector<std::pair<std::size_t,std::vector<uint8_t>>> res{};
    std::size_t leavesnum=(data.size()+1)/2;
    std::vector<std::size_t> queries;
    queries=queries_;
    query_index_.clear();
    assert(queries[0] >= leavesnum-1);
    while(true){
        if(!queries[0]){
            break;
        }
        std::vector<std::size_t> new_positions{};
        std::size_t it=0;
        std::size_t lenth=queries.size();
        while(it<lenth){
            std::size_t it_position=queries[it];
            new_positions.push_back((it_position-1)/2);
            if((it_position&1)==0){
                query_index_.push_back(it_position-1);
                res.emplace_back(it_position-1,data[it_position-1]);
            } else{
                if((it==lenth-1)||((it_position+1)!=(queries[it+1]))){
                    query_index_.push_back(it_position+1);
                    res.emplace_back(it_position+1,data[it_position+1]);
                } else{
                    it+=1;
                }
            }
            it+=1;
        }
        std::swap(queries,new_positions);
    }
    return res;
}

template<typename FieldT>
std::vector<std::size_t> merkle<FieldT>::find_merkle_path_only_index(std::size_t allNodeSize) {
    std::vector<std::size_t> res;
    std::size_t leavesnum=(allNodeSize+1)/2;
    std::vector<std::size_t> queries;
    queries=queries_;
    assert(queries[0]>leavesnum-1);
    while(true){
        if(!queries[0]){
            break;
        }
        std::vector<std::size_t> new_positions{};
        std::size_t it=0;
        std::size_t lenth=queries.size();
        while(it<lenth){
            std::size_t it_position=queries[it];
            new_positions.push_back((it_position-1)/2);
            if((it_position&1)==0){
                res.emplace_back(it_position-1);
            } else{
                if((it==lenth-1)||((it_position+1)!=(queries[it+1]))){
                    res.emplace_back(it_position+1);
                } else{
                    it+=1;
                }
            }
            it+=1;
        }
        std::swap(queries,new_positions);
    }

    return res;
}

template<typename FieldT>
std::vector<std::pair<std::size_t,std::vector<uint8_t>>> merkle<FieldT>::find_merkle_path_by_index(const std::vector<std::vector<uint8_t>> &data,const std::vector<std::size_t>& query_index){
    std::vector<std::pair<std::size_t,std::vector<uint8_t>>> res;
    const std::size_t lenth=query_index.size();
    res.resize(lenth);
    for(std::size_t i=0;i<lenth;i++){
        res[i]=std::make_pair(query_index[i],data[query_index[i]]);
    }
    return res;
}

template<typename FieldT>
std::vector<std::size_t> merkle<FieldT>:: get_queries(std::size_t query_num,std::size_t domain_size) {
    std::vector<std::size_t> query_set;
    for(std::size_t i=0;i<query_num;i++){
        bool is_repeat= true;
        std::size_t val;
        while(is_repeat){
            val=std::rand()%domain_size;

            std::vector<std::size_t>::iterator it;
            it= std::find(query_set.begin(),query_set.end(),val);
            if(it==query_set.end()){
                is_repeat= false;
            }
        }
        query_set.emplace_back(val);
    }

    for(unsigned long & i : query_set){
        i+=(domain_size-1);
//        std::cout<<i<<" ";
    }
//    std::cout<<"\n";
    return query_set;
}

template<typename FieldT>
std::vector<std::pair<std::size_t, std::vector<uint8_t>>>
merkle<FieldT>::get_public_hash_postion(const std::vector<std::vector<uint8_t>> &data) {
    //    认为positions已排好序 且符合merkle树的查询范围
    // 获取要求查询的叶子节点的哈希
    std::vector<std::pair<std::size_t, std::vector<uint8_t>>>res;
        for(unsigned long position : queries_){
        res.emplace_back(position,data[position]);
    }
    return res;
}

template<typename FieldT>
bool merkle<FieldT>::verify_merkle_commit(const merkleTreeParameter& par) {
    const std::vector<uint8_t> root=par.commit_root;
    const std::vector<std::pair<std::size_t, std::vector<uint8_t>>> auxiliary_hash=par.auxiliary_hash;
    std::vector<std::pair<std::size_t, std::vector<uint8_t>>> public_hash=par.public_hash;
    blake3HASH<FieldT> hashFunction;
    std::size_t aux_it=0;
    while(true){
        std::vector<std::pair<std::size_t, std::vector<uint8_t>>> new_public{};
        std::size_t it=0;

        std::size_t lenth=public_hash.size();
        if(public_hash[0].first==0){
            break;
        }
        while(it<lenth){
            std::size_t it_position=public_hash[it].first;
            std::vector<uint8_t> left_hash;
            std::vector<uint8_t> right_hash;
            if((it_position&1)==0){
                // 在右节点 左节点必不在 在auxiliary里找
//                res.emplace_back(it_position-1,data[it_position-1]);
                right_hash.assign(public_hash[it].second.begin(),public_hash[it].second.end());
                left_hash.assign(auxiliary_hash[aux_it].second.begin(),auxiliary_hash[aux_it].second.end());
//                assert(auxiliary_hash[aux_it].first==it_position-1);
                aux_it++;
            } else{
//                在左节点
                left_hash.assign(public_hash[it].second.begin(),public_hash[it].second.end());
                if((it==lenth-1)||((it_position+1)!=(public_hash[it+1].first))){
//                    右节点不在 在auxiliary找
                    right_hash.assign(auxiliary_hash[aux_it].second.begin(),auxiliary_hash[aux_it].second.end());
//                    assert(auxiliary_hash[aux_it].first==it_position+1);
                    aux_it++;
                } else{
                    right_hash.assign(public_hash[it+1].second.begin(),public_hash[it+1].second.end());
                    it+=1;
                }
            }
//            std::vector<uint8_t> parent_hash{this->HashFunction->two_to_one_hash(left_hash,right_hash)};
            std::vector<uint8_t> parent_hash=std::move(hashFunction.two_to_one_hash(left_hash,right_hash));
            new_public.emplace_back((it_position-1)/2,parent_hash);
            it+=1;
        }
        std::swap(public_hash,new_public);
    }
    if(public_hash[0].second==root){
        return true;
    } else{
        return false;
    }
}

template<typename FieldT>
merkleTreeParameter merkle<FieldT>::create_merklePar_of_matrix(const std::vector<std::vector<FieldT>>& matrix_data) {
    merkleTreeParameter res;
    this->create_tree_of_matrix(matrix_data);
//    std::cout<<"create_tree_suc\n";
    res.auxiliary_hash=std::move(this->find_merkle_path(this->allNodes_));
//    std::cout<<"auxiliary_hash_suc\n";
    res.public_hash=std::move(this->get_public_hash_postion(this->allNodes_));
//    std::cout<<"public_hash_suc\n";
    res.commit_root=this->allNodes_[0];
    res.path_lenth=res.auxiliary_hash.size()+1;
    return res;
}

template<typename FieldT>
merkleTreeParameter merkle<FieldT>::create_merklePar_of_vec(const std::vector<FieldT>& vec_data) {
    merkleTreeParameter res;
    this->create_tree_of_vec(vec_data);
    check_merkle_tree_correct(this->allNodes_);
//    std::cout<<"create_tree_suc\n";
    res.auxiliary_hash=std::move(this->find_merkle_path(this->allNodes_));
//    std::cout<<"auxiliary_hash_suc\n";
    res.public_hash=std::move(this->get_public_hash_postion(this->allNodes_));
//    std::cout<<"public_hash_suc\n";
    res.commit_root=this->allNodes_[0];
    res.path_lenth=res.auxiliary_hash.size()+1;
    return res;
}

template<typename FieldT>
merkleTreeParameter merkle<FieldT>::create_merklePar_of_vec_by_index(const std::vector<FieldT> &vec_data,
                                                                     const std::vector<std::size_t> &auxiliary_pos) {
    merkleTreeParameter res;
    this->create_tree_of_vec(vec_data);
//    std::cout<<"create_tree_suc\n";
    res.auxiliary_hash=std::move(this->find_merkle_path_by_index(this->allNodes_,auxiliary_pos));
//    std::cout<<"auxiliary_hash_suc\n";
    res.public_hash=std::move(this->get_public_hash_postion(this->allNodes_));
//    std::cout<<"public_hash_suc\n";
    res.commit_root=this->allNodes_[0];
    res.path_lenth=res.auxiliary_hash.size()+1;
    return res;
}

template<typename FieldT>
merkleTreeParameter merkle<FieldT>::create_merklePar_of_mat_by_index(const std::vector<std::vector<FieldT>>& matrix_data,
                                                                     const std::vector<std::size_t> &auxiliary_pos) {
    merkleTreeParameter res;
    this->create_tree_of_matrix(matrix_data);
//    std::cout<<"create_tree_suc\n";
    res.auxiliary_hash=std::move(this->find_merkle_path_by_index(this->allNodes_,auxiliary_pos));
//    std::cout<<"auxiliary_hash_suc\n";
    res.public_hash=std::move(this->get_public_hash_postion(this->allNodes_));
//    std::cout<<"public_hash_suc\n";
    res.commit_root=this->allNodes_[0];
    res.path_lenth=res.auxiliary_hash.size()+1;
    return res;
}



}
