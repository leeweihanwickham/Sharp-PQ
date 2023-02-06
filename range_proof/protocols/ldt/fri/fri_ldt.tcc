#include <libff/common/profiling.hpp>
#include <libff/common/utils.hpp>
#include <utility>
#include "range_proof/algebra/field_subset/subgroup.hpp"
#include "fri_ldt.hpp"


namespace range_proof {


template<typename FieldT>
FieldT FRI_verifier<FieldT>::getChallenge() {
    challenges.push_back(FieldT::random_element());
    return challenges.back();
}

template<typename FieldT>
bool FRI_verifier<FieldT>::verify(std::vector<std::size_t> query_list,
                                  FRI_prover<FieldT> *p, const std::vector<FieldT> &final_poly_coeffs) {
    this->prover = p;
    this->res = this->prover->res;
    for (std::size_t i = 0 ; i < 30; i++)
    {
        this->merkelTree[i] = this->prover->merkelTree[i];
    }
    this->pars.resize(this->prover->pars.size());
    for (std::size_t i = 0; i < this->prover->pars.size(); i++)
    {
        this->pars[i] = this->prover->pars[i];
    }

    std::size_t size_v = domain_.num_elements();

    FieldT shift = domain_.shift();
    /** whats the use of a? **/
    // a is used to generate a generator
    field_subset<FieldT> a(size_v, FieldT::one());
    FieldT generator = a.generator();

    std::size_t d = poly_degree_bound;
    std::size_t round_number = localization_parameter_array.size();
    for (std::size_t i = 0; i < round_number; i++) {
        std::size_t eta = localization_parameter_array[i];
        d >>= eta;

        for (auto &j: query_list) {
            j %= size_v >> eta;
        }
        std::sort(query_list.begin(), query_list.end());
        std::vector<std::size_t> query;
        query.push_back(query_list[0]);
        for (std::size_t j = 1; j < query_list.size(); j++) {
            if (query_list[j] != query_list[j - 1]) {
                query.push_back(query_list[j]);
            }
        }
        query_list = query;
        //
        for (std::size_t j = 0; j < query.size(); j++) {
            std::vector<FieldT> tmp;
            // q[j] + x * (size_v >> 2^eta)
            for (std::size_t k = query[j]; k < size_v; k += (size_v >> eta)) {
                // a_i * omega^{k}, k = q[j] + x * (size_v / 2^eta), x = [0, 2^{eta}-1]
                tmp.push_back(res[i][k]);
            }
            auto domain = field_subset<FieldT>(1 << eta, shift * (generator^query[j]));
            auto poly_coeff = IFFT_over_field_subset<FieldT>(tmp, domain);
            // compute the poly at point (challenges)
            FieldT v = poly_coeff.back();
            for (int k = poly_coeff.size() - 2; k >= 0; k--) {
                v = v * challenges[i] + poly_coeff[k];
            }

            tmp.clear();
            for (size_t k = query[j]; k < size_v; k += (size_v >> eta)) {
                tmp.push_back(res[i][k]);
            }

            // the core verification
            // res[i+1][0] is next round first queried value
            if (i < round_number - 1) {
                if (v != res[i + 1][query[j]]) {
                    return false;
                }
            }
            else {
                // check the degree of final poly
                std::size_t degree = 0;
                for (int k = final_poly_coeffs.size() - 1; k >= 0; k--) {
                    if (final_poly_coeffs[k] != FieldT::zero()) {
                        degree = k;
                        break;
                    }
                }
                if (d && degree >= d) {
                    return false;
                }
                // check the value of final poly
                // algorithm qin-jiu-shao
                FieldT x = (shift^(1 << eta)) * (generator^(query[j] << eta));
                FieldT poly_v = final_poly_coeffs.back();
                for (int k = final_poly_coeffs.size() - 2; k >= 0; k--) {
                    poly_v = poly_v * x + final_poly_coeffs[k];
                }
                if (v != poly_v) {
                    return false;
                }
            }
        }
        // TODO: proof size: FRI_trees related
        // rounds: localization_parameter_array.size()-2
        // every round has inter_repetition_num tree
        // all j leaves are consistent with root
        if (!this->merkelTree[i]->verify_merkle_commit(this->pars[i])) {
            return false;
        }

        /** what does back mean?
         * the computation of v?**/
        // v.evluation_at_point(challenges[i]), challenges[i]=\alpha_i
        for (size_t j = 0; j < eta; j++) {
            shift *= shift;
            generator *= generator;
        }
        size_v >>= eta;
    }
    return true;
}

// a null value
template<typename FieldT>
FRI_verifier<FieldT>::FRI_verifier(std::size_t poly_degree_bound,
                                   std::vector<std::size_t> localization_parameter_array,
                                   field_subset<FieldT> &domain):
        poly_degree_bound(poly_degree_bound),
        localization_parameter_array(std::move(localization_parameter_array)),
        domain_(domain) {}


// building a point-to-point communication channel
template<typename FieldT>
bool FRI_verifier<FieldT>::setProver(FRI_prover<FieldT> *p) {
    assert(p->verifier == this);
    this->prover = p;
    return true;
}

template<typename FieldT>
FRI_prover<FieldT>::FRI_prover(const polynomial<FieldT> &poly,
                               std::vector<std::size_t> localization_parameter_array,
                               FRI_verifier<FieldT> *verifier,
                               field_subset<FieldT> &domain) :
        localization_parameter_array(std::move(localization_parameter_array)),
        verifier(verifier),
        domain_(domain) {
    interpolateValues[0] = std::make_shared<std::vector<FieldT>>(FFT_over_field_subset(poly.coefficients(), domain));
}

template<typename FieldT>
FRI_prover<FieldT>::FRI_prover(polynomial<FieldT> &&poly,
                               std::vector<std::size_t> localization_parameter_array,
                               FRI_verifier<FieldT> *verifier,
                               field_subset<FieldT> &domain) :
        localization_parameter_array(std::move(localization_parameter_array)),
        verifier(verifier),
        domain_(domain) {
    interpolateValues[0] = std::make_shared<std::vector<FieldT>>(FFT_over_field_subset(poly.coefficients(), domain));
}

template<typename FieldT>
FRI_prover<FieldT>::FRI_prover(const std::shared_ptr<std::vector<FieldT>> value,
                               std::vector<std::size_t> localization_parameter_array,
                               FRI_verifier<FieldT> *verifier, field_subset<FieldT> &domain) :
        localization_parameter_array(std::move(localization_parameter_array)),
        verifier(verifier),
        domain_(domain) {
    interpolateValues[0] = value;
}

// try if i ==0,...
// if i !=0...
// {for j = ...}
template<typename FieldT>
void FRI_prover<FieldT>::prove(std::vector<std::size_t> query_list) {
    std::size_t size_v = domain_.num_elements();
    field_subset<FieldT> domain = domain_;
    FieldT shift = domain_.shift();
    std::size_t round_number = localization_parameter_array.size();
    this->pars.resize(round_number);
    FRI_tree_lenth=0;
    for (std::size_t i = 0; i < round_number; i++) {
        std::size_t eta = localization_parameter_array[i];

        for (auto &j: query_list) {
            j %= size_v >> eta;
        }
        std::sort(query_list.begin(), query_list.end());
        std::vector<std::size_t> query;
        query.push_back(query_list[0]);
        for (std::size_t j = 1; j < query_list.size(); j++) {
            if (query_list[j] != query_list[j - 1]) {
                query.push_back(query_list[j]);
            }
        }
        query_list = query;
        for (auto &j: query) {
            j += (size_v >> eta) - 1;
        }

        std::vector<std::vector<FieldT>> value_for_commit;
        assert(size_v == interpolateValues[i]->size());

        // interpolateValues[i], the interpolations in i th round
        for (std::size_t j = 0; j < size_v; j += (size_v >> eta)) {
            // there are eta vectors in value_for_commit
            value_for_commit.push_back(std::vector<FieldT>());
            for (std::size_t k = 0; k < (size_v >> eta); k++) {
                // (*interpolateValues[i])[j + k]: the j+k th element in interpolateValues[i]
                value_for_commit.back().push_back((*interpolateValues[i])[j + k]);
            }
        }

        this->merkelTree[i].reset(new merkle<FieldT>(
                size_v >> eta,
                query,
                true
        ));
        this->pars[i] = this->merkelTree[i]->create_merklePar_of_matrix(value_for_commit);
        FRI_tree_lenth+=this->pars[i].path_lenth;
        /**how to represent the multiple challenge
         * in the FRI of IPA**/
        FieldT alpha = verifier->getChallenge();
        size_v >>= eta;
        // the whole evaluation on the next codeword domain
        interpolateValues[i + 1] = evaluate_next_f_i_over_entire_domain(interpolateValues[i], domain,
                                                                        1 << eta, alpha);

        for (std::size_t j = 0; j < eta; j++) {
            shift *= shift;
        }
        domain = field_subset<FieldT>(size_v, shift);
    }

    this->final_poly_coeffs = IFFT_over_field_subset<FieldT>(*interpolateValues[round_number], domain);
}


template<typename FieldT>
void FRI_prover<FieldT>::query(std::vector<std::size_t> query_list) {
    this->res.clear();
    //this->hashes.clear();
    std::size_t round_number = this->localization_parameter_array.size();

    for (std::size_t i = 0; i < round_number; i++) {
        this->res.push_back(std::map<std::size_t, FieldT>());
        std::size_t size = this->interpolateValues[i]->size();
        std::size_t eta = this->localization_parameter_array[i];

        // turn the 3rd position to 1st
        for (auto &j: query_list) {
            j %= (size >> eta);
        }
        // delete the repetition, make the query list unique
        std::sort(query_list.begin(), query_list.end());
        std::vector<std::size_t> query;
        query.push_back(query_list[0]);
        for (std::size_t j = 1; j < query_list.size(); j++) {
            if (query_list[j] != query_list[j - 1]) {
                query.push_back(query_list[j]);
            }
        }
        query_list = query;
        // delete the repetition, make the query list unique
        for (auto &j: query) {
            for (std::size_t k = j; k < size; k += (size >> eta)) {
                // a_i * omega^{k}, this is exactly the k-th value of the entire interpolatition
                this->res[i][k] = (*this->interpolateValues[i])[k];
            }
        }
        // used for merkle tree lookup
        for (auto &j: query) {
            j += (size >> eta) - 1;
        }
    }
}

template<typename FieldT>
Inner_product_verifier<FieldT>::Inner_product_verifier(
//        const std::vector<polynomial<FieldT>> &s,
        const std::vector<polynomial<FieldT>> &&s,
        field_subset<FieldT> computed_domain,
//        std::vector<std::vector<FieldT>> &v_evluation_on_codeword_domain,
//        std::vector<std::vector<FieldT>> &s_evluation_on_codeword_domain,
        const std::vector<std::vector<FieldT>> &&v_evluation_on_codeword_domain,
        const std::vector<std::vector<FieldT>> &&s_evluation_on_codeword_domain,
        std::size_t padding_degree,
        std::size_t poly_bound,
        std::vector<std::size_t> localization_parameter_array,
        field_subset<FieldT> ldt_domain,
        FieldT value,
        std::size_t round):
        s(s),
        v_evluation_on_codeword_domain(v_evluation_on_codeword_domain),
        s_evluation_on_codeword_domain(s_evluation_on_codeword_domain),
        compute_domain(computed_domain),
        padding_degree(padding_degree),
        value(value),
        ldt_domain(ldt_domain),
        round(round) {

    // TODO change
    //this->Z_H = polynomial<FieldT>(compute_domain);

    FieldT shift = ldt_domain.shift();
    for (std::size_t j = 0; j < localization_parameter_array[0]; j++) {
        shift *= shift;
    }

    this->first_round_dim = localization_parameter_array[0];
    field_subset<FieldT> domain(ldt_domain.num_elements() >> first_round_dim, shift);

    std::vector<std::size_t> param;
    for (std::size_t i = 1; i < localization_parameter_array.size(); i++) {
        param.push_back(localization_parameter_array[i]);
    }

    for (std::size_t i = 0; i < round; i++) {
        this->fri_verifier.push_back(new FRI_verifier<FieldT>(poly_bound >> first_round_dim,
                                                              param, domain));
    }
}

template<typename FieldT>
FRI_verifier<FieldT> *Inner_product_verifier<FieldT>::getFriVerifier(std::size_t idx) {
    return this->fri_verifier[idx];
}


template<typename FieldT>
bool Inner_product_verifier<FieldT>::verify(std::vector<std::size_t> query_list, Inner_product_prover<FieldT> *ip_prover) {

    libff::enter_block("Setting parameters");
    this->prover = ip_prover;
    this->h_tree = this->prover->h_tree;
    this->par_for_htree = this->prover->par_for_htree;

    field_subset<FieldT> a(ldt_domain.num_elements(), FieldT::one());
    FieldT generator = a.generator();
    std::size_t size = ldt_domain.num_elements();

    for (auto &i: query_list) {
        i %= (size >> first_round_dim);
    }
    std::vector<std::size_t> tmp;
    std::sort(query_list.begin(), query_list.end());
    tmp.push_back(query_list[0]);
    for (std::size_t i = 1; i < query_list.size(); i++) {
        if (query_list[i] != query_list[i - 1]) {
            tmp.push_back(query_list[i]);
        }
    }
    query_list = tmp;
    libff::leave_block("Setting parameters");

    // TODO: v and s can fuyong
    libff::enter_block("Computig evaluations of v and s");

    libff::leave_block("Computig evaluations of v and s");

    libff::enter_block("Verifying");

    FieldT shift = ldt_domain.shift();
    vanishing_polynomial<FieldT> vanishing_polynomial(this->compute_domain);
    std::vector<FieldT> h_eva = FFT_over_field_subset(this->prover->h.coefficients(),ldt_domain);
    std::vector<FieldT> ldt_element_vec = ldt_domain.all_elements();

    for (std::size_t i = 0; i < round; i++) {

        prover->fri_prover[i]->query(query_list);
        if (!fri_verifier[i]->verify(query_list,fri_verifier[i]->prover, prover->fri_prover[i]->final_poly_coeffs)) {
            return false;
        }

        libff::enter_block("Verify the first round");
        // verification of the first round
        std::vector<std::size_t> query;
        for (auto &l: query_list) {

            //libff::enter_block("222");
            std::vector<FieldT> tmp;
            for (std::size_t j = l; j < size; j += (size >> first_round_dim)) {

                //libff::enter_block("333");
                //FieldT x = ldt_domain.all_elements()[j];
                FieldT x = ldt_element_vec[j];
                //assert(x == x1);
                FieldT f = FieldT::zero();
                //libff::leave_block("333");

                for (std::size_t k=0; k<s.size() ; k++ )
                {
                    auto middle = v_evluation_on_codeword_domain[k][j];
                    f+= s_evluation_on_codeword_domain[k][j] * middle;
                }

                // TODO change Z_H to vanishing_polynomial
                FieldT h = h_eva[j];
                //FieldT h = prover->h.evaluation_at_point(x);
                //assert(h1 == h);

                FieldT p = (FieldT(compute_domain.num_elements()) * (f - vanishing_polynomial.evaluation_at_point(x) * h) - value) * x.inverse();
                tmp.push_back(f * (x^padding_degree) + random_pair[i].first * h * (x^(padding_degree + s[0].degree()))
                              + random_pair[i].second * p * (x^(padding_degree + s[0].degree())));
                query.push_back(l + size - 1);
            }

            //libff::leave_block("222");
            auto domain = field_subset<FieldT>(1 << first_round_dim, shift * (generator^l));
            std::vector<FieldT> poly_coeff = IFFT_over_field_subset<FieldT>(tmp, domain);
            FieldT v = poly_coeff.back();

            //libff::enter_block("444");
            for (int j = poly_coeff.size() - 2; j >= 0; j--) {
                v = v * challenge[i] + poly_coeff[j];
            }
            //libff::leave_block("444");
            if (v != fri_verifier[i]->res[0][l]) {
                return false;
            }
        }
        libff::leave_block("Verify the first round");

        if (!h_tree->verify_merkle_commit(this->par_for_htree)) {
            return false;
        }
    }
    libff::leave_block("Verifying");
    return true;

}


template<typename FieldT>
std::pair<FieldT, FieldT> Inner_product_verifier<FieldT>::getRandomPair() {
    auto pair = std::pair<FieldT, FieldT>(FieldT::random_element(), FieldT::random_element());
    this->random_pair.push_back(pair);
    return pair;
}

template<typename FieldT>
FieldT Inner_product_verifier<FieldT>::getChallenge() {
    challenge.push_back(FieldT::random_element());
    return challenge.back();
}

template<typename FieldT>
Inner_product_prover<FieldT>::Inner_product_prover(const std::vector<polynomial<FieldT>> &&s,
                                                   const std::vector<polynomial<FieldT>> &&v,
                                                   //std::vector<std::vector<FieldT>> v_evaluation_on_codeword_domain,
                                                   std::vector<std::size_t> query_set,
                                                   std::vector<std::size_t>& localization_parameter_array,
                                                   std::size_t poly_bound,
                                                   Inner_product_verifier<FieldT> &verifier,
                                                   field_subset<FieldT> &ldt_domain,
                                                   std::size_t round):
        s(s), v(v),
        verifier(verifier),
        round(round) {
    h_tree_lenth=0;

    libff::enter_block("Computing vanishing_polynomial");

    vanishing_polynomial<FieldT> vanishing_polynomial(this->verifier.compute_domain);

    libff::leave_block("Computing vanishing_polynomial");

    libff::enter_block("Computing Polynomials for sumcheck");
    // The summation polynomial
    // TODO change
    libff::enter_block("Compute s_v");

    libff::enter_block("Compute evaluation");
    // version: use the evaluation to compute
    std::vector<FieldT> s_v_evaluation;
    s_v_evaluation.resize(ldt_domain.num_elements(),FieldT::zero());

    for (std::size_t j = 0; j < s.size(); j ++)
    {
        for (std::size_t i = 0; i < s_v_evaluation.size(); i ++)
        {
            auto middle = (this->verifier.s_evluation_on_codeword_domain.at(j)[i] * this->verifier.v_evluation_on_codeword_domain.at(j)[i]);
            s_v_evaluation[i] += middle;
        }
    }

    libff::leave_block("Compute evaluation");

    libff::enter_block("delete zero");
    std::vector<FieldT> s_v_vec_2 = IFFT_over_field_subset(s_v_evaluation,ldt_domain);

    s_v_evaluation.size();
    s_v_evaluation.shrink_to_fit();

    while (true) {
        if (s_v_vec_2.back() != FieldT(0)) {
            break;
        }
        s_v_vec_2.pop_back();
    }

    polynomial<FieldT> s_v = polynomial<FieldT> (std::move(s_v_vec_2));

    libff::leave_block("delete zero");

    libff::leave_block("Compute s_v");

    libff::enter_block("Compute h and p");
    // compute polynomial h and p
    // It's a shang, instead of yushu

    std::pair<polynomial<FieldT>, polynomial<FieldT>> h_and_g =
            polynomial_over_vanishing_polynomial<FieldT>(s_v, vanishing_polynomial);

    this-> h = h_and_g.first;
    polynomial<FieldT> p = h_and_g.second;
    p.multiply_coefficients_by(FieldT(this->verifier.compute_domain.num_elements()));

    // It's p/x, remove and shift
    p.remove_term(0);
    libff::leave_block("Compute h and p");

    libff::leave_block("Computing Polynomials for sumcheck");

    libff::enter_block("Generate query set");
    for (auto &i: query_set) {
        i %= (ldt_domain.num_elements() >> localization_parameter_array[0]);
    }
    std::vector<std::size_t> tmp;
    std::sort(query_set.begin(), query_set.end());
    tmp.push_back(query_set[0]);
    for (std::size_t i = 1; i < query_set.size(); i++) {
        if (query_set[i] != query_set[i - 1]) {
            tmp.push_back(query_set[i]);
        }
    }
    query_set = tmp;

    for (auto & i : query_set)
    {
        i += ((ldt_domain.num_elements() >> localization_parameter_array[0]) - 1);
    }
    libff::leave_block("Generate query set");

    libff::enter_block("Committing to Secret Polynomials for IPA");

    // split every v_evaluations into 1ull<<local[0] pieces
    // construct only 1 merkle tree
//    v_trees.resize(1);
//    std::vector<std::vector<FieldT>> v_values;
//    v_values.resize((1ull << localization_parameter_array[0]) * v.size());
//    for (std::size_t i = 0; i < v.size(); i++)
//    {
//        for (std::size_t j = 0; j < (1ull << localization_parameter_array[0]); j ++){
//            for (std::size_t k = 0; k < (ldt_domain.num_elements() >> localization_parameter_array[0]); k ++){
//                v_values[(i*(1ull<<localization_parameter_array[0]))+j].push_back
//                (this->verifier.v_evluation_on_codeword_domain[i][k+j*(ldt_domain.num_elements() >> localization_parameter_array[0])]);
//            }
//        }
//    }
//
//    v_trees[0].reset(new merkle<FieldT>(
//            v_values[0].size(),
//            query_set,
//            true
//    ));
//
//    this->pars_for_vtrees.resize(1);
//    this->pars_for_vtrees[0] = v_trees[0]->create_merklePar_of_matrix(v_values);
//    v_tree_length = this->pars_for_vtrees[0].path_lenth;

    libff::leave_block("Committing to Secret Polynomials for IPA");

    libff::enter_block("Committing to h polynomial for IPA");
    std::vector<std::vector<FieldT>> h_value;
    h_value.resize(1ull << localization_parameter_array[0]);
    std::vector<FieldT> h_evaluation = FFT_over_field_subset(h.coefficients(), ldt_domain);
    for (std::size_t i = 0; i < (1ull << localization_parameter_array[0]) ; i++)
    {
        for (std::size_t j = 0; j < ((ldt_domain.num_elements() >> localization_parameter_array[0])); j++ )
        {
            h_value[i].push_back(h_evaluation[j + i*((ldt_domain.num_elements() >> localization_parameter_array[0]))]);
        }
    }

    h_tree.reset(new merkle<FieldT>(
            h_value[0].size(),
            query_set,
            true
    ));
    this->par_for_htree = this->h_tree->create_merklePar_of_matrix(h_value);
    h_tree_lenth = this->par_for_htree.path_lenth;
    libff::leave_block("Committing to h polynomial for IPA");

    libff::enter_block("Proving the first round for sumcheck");
    // TODO check why the time is large, use FFT to try
    // compute poly after padding
    // This is because FRI only support 2^k
    // every polynomial v_s * x ^{padding_degree}

    //std::size_t padding_degree = poly_bound - s[0].degree() - v[0].degree() - 1;
    std::size_t padding_degree = this->verifier.padding_degree;

    for (std::size_t i = 0; i < round; i++) {
        std::pair<FieldT, FieldT> r = verifier.getRandomPair();

        std::vector<polynomial<FieldT>> vvs;
        vvs.resize(v.size());

        for (std::size_t j = 0; j< v.size() ; j++) {
            vvs[j] = v[j];
            vvs[j].multiply_x(padding_degree);
        }

        polynomial<FieldT> hh = h;
        hh.multiply_coefficients_by(r.first);
        hh.multiply_x(padding_degree + s[0].degree());
        polynomial<FieldT> pp = p;
        pp.multiply_coefficients_by(r.second);
        pp.multiply_x(padding_degree + s[0].degree());

        polynomial<FieldT> poly;
        poly = s_v;
        poly.multiply_x(padding_degree);
        
        poly+= hh + pp;

        // first round
        std::shared_ptr<std::vector<FieldT>> interpolateValue =
                std::make_shared<std::vector<FieldT>>(FFT_over_field_subset(poly.coefficients(), ldt_domain));
        FRI_verifier<FieldT> *fri_verifier = verifier.getFriVerifier(i);
        std::vector<std::size_t> param;
        for (std::size_t j = 1; j < localization_parameter_array.size(); j++) {
            param.push_back(localization_parameter_array[j]);
        }
        FieldT alpha = verifier.getChallenge();
        std::size_t eta = localization_parameter_array[0];

        std::shared_ptr<std::vector<FieldT>> next_interpolate = evaluate_next_f_i_over_entire_domain(interpolateValue,
                                                                                                     ldt_domain, 1 << eta, alpha);
        FieldT shift = ldt_domain.shift();
        for (std::size_t j = 0; j < eta; j++) {
            shift *= shift;
        }
        field_subset<FieldT> domain(ldt_domain.num_elements() >> eta, shift);
        // construct fri_prover
        this->fri_prover.push_back(new FRI_prover<FieldT>(next_interpolate, param,
                                                          fri_verifier, domain));
        fri_verifier->setProver(this->fri_prover.back());

    }
    libff::leave_block("Proving the first round for sumcheck");

}

template<typename FieldT>
void Inner_product_prover<FieldT>::prove(std::vector<size_t> query_set) {
    FRI_tree_lenth=0;
    for (auto &i: this->fri_prover) {
        libff::enter_block("Proving the next round FRI");
        i->prove(query_set);
        FRI_tree_lenth+=i->FRI_tree_lenth;
        libff::leave_block("Proving the next round FRI");
    }
}

} // namespace libiop
