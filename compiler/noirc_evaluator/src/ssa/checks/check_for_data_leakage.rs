use acvm::acir::circuit::black_box_functions::BlackBoxFunc;
use noirc_errors::Span;
use noirc_errors::Location;
use noirc_errors::call_stack::CallStack;
use crate::ssa::ir::integer::IntegerConstant;
use crate::ssa::ir::instruction::BinaryOp;
use crate::errors::{InternalBug, SsaReport};
use crate::ssa::ir::basic_block::BasicBlockId;
use crate::ssa::ir::function::Function;
use crate::ssa::ir::instruction::{Instruction, InstructionId, Intrinsic};
use crate::ssa::ir::value::ValueId;
use crate::ssa::ir::value::Value;
use crate::ssa::ssa_gen::Ssa;
use crate::ssa::Visibility; 
use noirc_frontend::hir_def::function::FunctionSignature;
use noirc_frontend::Type;
use crate::ssa::ir::types::Type as ssa_Type;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::collections::HashMap;
use std::cmp::min;

impl Ssa{

    pub(crate) fn check_for_data_leakage(
        &mut self,
    ) -> Vec<SsaReport>{
        let func_sigs = &self.function_signatures.clone().unwrap();
        self.normalize_ids();
        self.functions
            .values()
            .zip(func_sigs)
            .map(|pair| (pair.0.id(),pair.1))
            .flat_map(|fid_sig_pair| {
                let function_to_process = &self.functions[&fid_sig_pair.0];
                check_for_data_leakage_within_function(function_to_process,fid_sig_pair.1)
            })
            .collect()
    }
}

// H = min (sum (priv_vals), Hcurr, bitwidht_res )
#[derive(Debug)]
pub(crate) struct ValueInfo {
    pub vis: Visibility,
    // instruction that generates this value 
    pub instr: Option<InstructionId>,
    pub entropy: u64,
    // private values that somehow are mixed in this val
    pub priv_vals: Option<HashSet<ValueId>>,
}

impl ValueInfo {
    fn new(vis: Visibility, instr: Option<InstructionId>,entropy: u64, priv_vals: Option<HashSet<ValueId>>) -> Self{
        ValueInfo {
            vis: vis,
            instr: instr,
            entropy: entropy,
            priv_vals: priv_vals
        }
    }
}


fn check_for_data_leakage_within_function(
    function: &Function,
    func_sig: &FunctionSignature,
) -> Vec<SsaReport> {

    let mut warnings: Vec<SsaReport> = Vec::new();


    let tags_map = make_tags_map(function, function.entry_block(), func_sig);
    tags_map_pretty_printer(&tags_map, function);
    let mut bad_instr: Vec<InstructionId> = Vec::new();

    let instructions = function.dfg[function.entry_block()].instructions();
    // when we have simple return tags_map_analysis doesn't insert terminator instruction
    // so we need helper flag
    let mut terminator_flag = false;
    for ret_val in function.returns().unwrap().iter(){
        if function.dfg.get_numeric_constant(*ret_val).is_some(){
            continue;
        }
        let result = tags_map.get(ret_val).expect("error occured, there is no value in tags map with such id");
        if (result.vis == Visibility::Private) ||
            (result.entropy <= 80 && result.entropy > 0) {
            tags_map_analysis(&tags_map, ret_val.clone(),&mut bad_instr, function);
            terminator_flag = true;        
                
        }
    }
    let mut all_locations = Vec::new();
    let mut seen_locations = HashSet::new();
    let mut final_entropies = Vec::new();
    let mut final_private_values = Vec::new();  // Vec<Vec<String>>

    if !bad_instr.is_empty() {
        bad_instr.sort();
        let mut grouped: BTreeMap<CallStack, (InstructionId, CallStack)> = BTreeMap::new();
        for &instr_id in &bad_instr {
            let call_stack = function.dfg.get_instruction_call_stack(instr_id);
            if call_stack.is_empty() { continue; }
            let normalized = normalize_call_stack(&call_stack);
            grouped.entry(normalized).or_insert_with(|| (instr_id, call_stack));
        }

        for (_, (instr_id, original_stack)) in &grouped {
            for loc in original_stack.iter() {
                let normalized_loc = Location {
                    span: Span::inclusive(loc.span.start(), loc.span.start()),
                    file: loc.file,
                };
                if seen_locations.insert(normalized_loc) {
                    all_locations.push(loc.clone());
                }
            }
        }
    }

    if terminator_flag {
        if let Some(terminator) = function.dfg[function.entry_block()].terminator() {
            let term_call_stack = function.dfg.get_call_stack(terminator.call_stack());
            for loc in term_call_stack.iter() {
                let normalized_loc = Location {
                    span: Span::inclusive(loc.span.start(), loc.span.start()),
                    file: loc.file,
                };
                if seen_locations.insert(normalized_loc) {
                    all_locations.push(loc.clone());
                }
            }

            for ret_val in function.returns().unwrap().iter() {
                if let Some(info) = tags_map.get(ret_val) {
                    final_entropies.push(info.entropy);
                    let priv_strings = info.priv_vals.as_ref()
                        .map(|set| {
                            let mut ids: Vec<ValueId> = set.iter().copied().collect();
                            ids.sort();
                            ids.into_iter().map(|id| format!("{}", id)).collect()
                        })
                        .unwrap_or_default();
                    final_private_values.push(priv_strings);
                }
            }
        }
    }

    if !all_locations.is_empty() {
        warnings.push(SsaReport::Bug(InternalBug::DataLeak {
            call_stack: all_locations,
            entropy: final_entropies,
            private_values: final_private_values,
        }));
    }
    warnings
}

fn normalize_call_stack(call_stack: &CallStack) -> CallStack {
    call_stack.iter().map(|loc| {
        let start = loc.span.start(); 
        Location {
            span: Span::inclusive(start, start),
            file: loc.file,
        }
    }).collect()
}

// analyse instruction and set a tag to result value, add tag in variable tags map
fn add_result_tag(
    function: &Function,
    instruction: &Instruction,
    instruction_id: InstructionId,
    tags_map: &mut BTreeMap<ValueId,ValueInfo>,
    ids_vec: &mut Vec<ValueId>,
){
    match instruction{
        Instruction::Binary(..) => {
            let arg1 = ids_vec[0];
            let arg2 = ids_vec[1];
            let res = ids_vec[2];
            if function.dfg.get_numeric_constant(arg1).is_some(){
                tags_map.insert(arg1, ValueInfo::new(Visibility::Public,None,0,None));
            }
            if function.dfg.get_numeric_constant(arg2).is_some(){
                tags_map.insert(arg2, ValueInfo::new(Visibility::Public,None,0,None));
            }
            let tag1 = tags_map.get(&arg1).unwrap();
            let tag2 = tags_map.get(&arg2).unwrap();
            let (entropy, priv_vals) = calculate_entropy(function,res,instruction, &vec![tag1,tag2],&vec![arg1,arg2],tags_map);
            if tag1.vis == Visibility::Private || tag2.vis == Visibility::Private{
                tags_map.insert(res, ValueInfo::new(Visibility::Private,Some(instruction_id),entropy,priv_vals));
            } else {
                tags_map.insert(res,ValueInfo::new(Visibility::Public,Some(instruction_id),entropy,priv_vals));
            }
        },
        Instruction::Cast(..)
        | Instruction::Not(..)
        | Instruction::Truncate { .. } => {
            let arg = ids_vec[0];
            if function.dfg.get_numeric_constant(arg).is_some(){
                tags_map.insert(arg, ValueInfo::new(Visibility::Public,None,0,None));
            }
            let res = ids_vec[1];
            let tag = tags_map.get(&arg).unwrap();
            let (entropy, priv_vals) = calculate_entropy(function,res,instruction, &vec![tag],&vec![arg],tags_map);
            tags_map.insert(res, ValueInfo::new(tag.vis,Some(instruction_id),entropy,priv_vals));
        },
        Instruction::ArrayGet { .. } => {
            let arr = ids_vec[0];
            let _ind = ids_vec[1];
            if function.dfg.get_numeric_constant(_ind).is_some() {
                tags_map.insert(_ind, ValueInfo::new(Visibility::Public,None,0,None));
            }
            let res = ids_vec[2];
            let tag = tags_map.get(&arr).unwrap();
            let ind_tag = tags_map.get(&_ind).unwrap();
            let (entropy, priv_vals) = calculate_entropy(function,res,instruction, &vec![tag,ind_tag],&vec![arr,_ind],tags_map);
            tags_map.insert(res,ValueInfo::new(tag.vis,Some(instruction_id),entropy,priv_vals));
        }
        Instruction::ArraySet {..} => {
            let arr = ids_vec[0];
            let _ind = ids_vec[1];
            let val = ids_vec[2];
            let res = ids_vec[3];
            if function.dfg.get_numeric_constant(_ind).is_some() {
                tags_map.insert(_ind, ValueInfo::new(Visibility::Public,None,0,None));
            }
            if function.dfg.get_numeric_constant(val).is_some() {
                tags_map.insert(val, ValueInfo::new(Visibility::Public,None,0,None));
            }
            let val_tag = tags_map.get(&val).unwrap();
            let ind_tag = tags_map.get(&_ind).unwrap();
            let arr_tag = tags_map.get(&arr).unwrap();
            let mut res_vis = Visibility::Public;
            if arr_tag.vis == Visibility::Private || val_tag.vis == Visibility::Private {res_vis = Visibility::Private}
            let (entropy, priv_vals) = calculate_entropy(function,res,instruction, &vec![arr_tag,ind_tag,val_tag],&vec![arr,_ind,val],tags_map);
            tags_map.insert(res,ValueInfo::new(res_vis,Some(instruction_id),entropy,priv_vals));

        }
        Instruction::MakeArray { .. } => {
            let mut vis = Visibility::Public;
            let elem_ids = &ids_vec[0..ids_vec.len()-1];
            for element in elem_ids {
                if tags_map.get(element).is_none() {
                   if function.dfg.get_numeric_constant(*element).is_some() {
                        tags_map.insert(*element,ValueInfo::new(Visibility::Public,None,0,None));
                    } 
                } else {
                    if tags_map.get(element).unwrap().vis == Visibility::Private {
                        vis = Visibility::Private;
                    }
                }
            }
            let vinfo_elems: Vec<&ValueInfo> = elem_ids.iter().map(|id| tags_map.get(id).unwrap()).collect();
            let (entropy, priv_vals) = calculate_entropy(function,ids_vec[ids_vec.len()-1],instruction, &vinfo_elems,&elem_ids.to_vec(),tags_map);
            tags_map.insert(ids_vec[ids_vec.len()-1], ValueInfo::new(vis,Some(instruction_id),entropy,priv_vals));
        }
        Instruction::Call { .. } => {
            let function_value = &function.dfg[ids_vec[0]];
            match function_value {
                Value::Intrinsic (intrinsic) => {
                    match intrinsic {
                        Intrinsic::BlackBox( blackbox_func ) => {
                            let ids_vec_len = ids_vec.len();
                            let res_info = blackbox_function_analysis(function,blackbox_func, &ids_vec[1..ids_vec_len-1],ids_vec[ids_vec_len-1], tags_map);
                            tags_map.insert(ids_vec[ids_vec.len()-1],ValueInfo::new(res_info.0,Some(instruction_id),res_info.1,res_info.2));
                        },
                        Intrinsic::ToRadix(..) |
                        Intrinsic::ToBits(..) => {
                            let arg_info = tags_map.get(&ids_vec[1]).unwrap();
                            tags_map.insert(ids_vec[ids_vec.len()-1],ValueInfo::new(arg_info.vis,Some(instruction_id),arg_info.entropy,arg_info.priv_vals.clone()));
                        }
                       _ => {
                            tags_map.insert(ids_vec[ids_vec.len()-1],ValueInfo::new(Visibility::Public,Some(instruction_id),0,None));

                       }
                    }
                },
                _ => {}
                
            }
            
        }
        _ => {}
    }
}

///add main function arguments in tags_map base on their visibility
fn add_main_args_in_tags_map(
    tags_map: &mut BTreeMap<ValueId,ValueInfo>,
    func_sig: &FunctionSignature,
    function: &Function,
){

    let mut args= Vec::new();

    for param in &func_sig.0{
        match &param.1 {
            // user structure parsing
            Type::DataType(definition, generics) => {
                let fields = definition.borrow().get_fields(generics).unwrap();
                for field in fields{
                    args.push((param.2, field.1));
                }
            },
            _ => {args.push((param.2, (param.1).clone()))},
        }
    }


    for (metadata,id) in (args).iter().zip(function.parameters()){
        let mut entropy: u64 = 0;
        if metadata.0 == Visibility::Private {
            let ssa_typ =function.dfg.type_of_value(*id);
            entropy = calculate_bitwidth(ssa_typ);
        }
        tags_map.insert(*id,ValueInfo::new(metadata.0,None,entropy,None));
    }
}

// Go through each instruction in the block and marking all variables
// tags map representing visibility of var, instruction that make this var and also entropy of this
// var in bits (u64)
fn make_tags_map(
    function: &Function,
    block: BasicBlockId,
    func_sig: &FunctionSignature,
) -> BTreeMap<ValueId, ValueInfo>{
    let instructions = function.dfg[block].instructions();

    let mut tags:BTreeMap<ValueId, ValueInfo> = BTreeMap::new();

    add_main_args_in_tags_map(&mut tags, func_sig,function);

    for instruction in instructions.iter() {
        let mut instruction_arguments_and_results = Vec::new();
        // Insert all instruction arguments
        function.dfg[*instruction].for_each_value(|value_id| {
            instruction_arguments_and_results.push(value_id); 
        });
        // And all results
        for value_id in function.dfg.instruction_results(*instruction).iter() {
            instruction_arguments_and_results.push(*value_id);
        }

        let mut instruction_arguments_and_results_copy = instruction_arguments_and_results.clone();

        add_result_tag(function,&function.dfg[*instruction],*instruction,&mut tags, &mut instruction_arguments_and_results_copy);

    }

    tags

}

fn blackbox_function_analysis(
    function: &Function,
    blackbox_function: &BlackBoxFunc,
    arguments: &[ValueId],
    res_id: ValueId,
    tags_map: &mut BTreeMap<ValueId, ValueInfo>,
) -> (Visibility,u64,Option<HashSet<ValueId>>){
   match blackbox_function {
        BlackBoxFunc::AES128Encrypt => {
            let _input = arguments[0];
            let _iv = arguments[1];
            let key = arguments[2];
            if function.dfg.get_numeric_constant(key).is_some(){
                tags_map.insert(key, ValueInfo::new(Visibility::Public,None,0,None));
            }
            let vinfo_elems: Vec<&ValueInfo> = arguments.iter().map(|id| tags_map.get(id).unwrap()).collect();
            let (entropy,priv_vals) = calculate_entropy_bbox(function, res_id, blackbox_function, &vinfo_elems, &vec![_input,_iv,key], tags_map);
            if tags_map.get(&key).unwrap().vis == Visibility::Public {
                return (Visibility::Private,entropy,priv_vals)
            } else {
                return (Visibility::Public,entropy,priv_vals)
            } 
        },
        BlackBoxFunc::Blake3 |
        BlackBoxFunc::Blake2s |
        BlackBoxFunc::Sha256Compression => {
            let vinfo_elems: Vec<&ValueInfo> = arguments.iter().map(|id| tags_map.get(id).unwrap()).collect();
            let (entropy,priv_vals) = calculate_entropy_bbox(function, res_id, blackbox_function, &vinfo_elems, &arguments.to_vec(), tags_map);
            return (Visibility::Public,entropy,priv_vals)

        }
        // NOTE: keccakf1600 and poseidon2perm are reversible 
        BlackBoxFunc::Keccakf1600 |
        BlackBoxFunc::Poseidon2Permutation => {
            let vinfo_elems: Vec<&ValueInfo> = arguments.iter().map(|id| tags_map.get(id).unwrap()).collect();
            let (entropy,priv_vals) = calculate_entropy_bbox(function, res_id, blackbox_function, &vinfo_elems, &arguments.to_vec(), tags_map);
            return (tags_map.get(&arguments[0]).unwrap().vis,entropy,priv_vals)
        }
        BlackBoxFunc::EmbeddedCurveAdd => {
            let mut visibility = Visibility::Public;
            for arg in arguments.iter() {
                if function.dfg.get_numeric_constant(*arg).is_some() {
                    tags_map.insert(*arg, ValueInfo::new(Visibility::Public,None,0,None));
                } else {
                    if tags_map.get(arg).unwrap().vis == Visibility::Private {visibility = Visibility::Private;}
                }
            }
            let vinfo_elems: Vec<&ValueInfo> = arguments.iter().map(|id| tags_map.get(id).unwrap()).collect();
            let (entropy,priv_vals) = calculate_entropy_bbox(function, res_id, blackbox_function, &vinfo_elems, &arguments.to_vec(), tags_map);
            return (visibility,entropy,priv_vals);
        },
        // NOTE: scalar is public -> depends on points visibility
        // scalar is private -> public (discrete logarithm problem)
        BlackBoxFunc::MultiScalarMul => {
            let points = arguments[0];
            let scalars = arguments[1];
            for arg in arguments.iter() {
                if function.dfg.get_numeric_constant(*arg).is_some() {
                    tags_map.insert(*arg, ValueInfo::new(Visibility::Public,None,0,None));
                }
            }
            let vinfo_elems: Vec<&ValueInfo> = arguments.iter().map(|id| tags_map.get(id).unwrap()).collect();
            let (entropy,priv_vals) = calculate_entropy_bbox(function, res_id, blackbox_function, &vinfo_elems, &arguments.to_vec(), tags_map);
            if tags_map.get(&scalars).unwrap().vis == Visibility::Private { return (Visibility::Public,entropy,priv_vals) }
            return (tags_map.get(&points).unwrap().vis,entropy,priv_vals)
        },
        // NOTE: logic is that parametrs of function 
        // dont compromise anything (since key is public, hash is hash
        // and signature is signature)
        BlackBoxFunc::EcdsaSecp256k1 |
        BlackBoxFunc::EcdsaSecp256r1 => {
            return (Visibility::Public,0,None)
        }

        _ => {
            return (Visibility::Public,0,None)
        }
    }
}

fn calculate_bitwidth (
    res_type: ssa_Type
) -> u64 {
    let mut res = 0;
    match res_type {
        ssa_Type::Array(types,len) => {
            let mut comp_type_bitwidth = 0;
            for typ in types.iter(){
                comp_type_bitwidth += calculate_bitwidth(typ.clone());
            }
            res = comp_type_bitwidth * (len as u64);
        }
        _ => {res = res_type.bit_size() as u64;}
    }
    res 
}

fn calculate_entropy_bbox (
    function: &Function,
    res_id: ValueId,
    blackbox_function: &BlackBoxFunc,
    vinfo_vec: &Vec<&ValueInfo>, 
    ids_vec: &Vec<ValueId>,
    tags_map: &BTreeMap<ValueId,ValueInfo>,
) -> (u64, Option<HashSet<ValueId>>){     
    let mut res_set = HashSet::<ValueId>::new();
    for (arg, vid) in vinfo_vec.iter().zip(ids_vec) {
        if arg.vis == Visibility::Private {

            if let Some(priv_vals) = arg.priv_vals.as_ref() {
                for &priv_val in priv_vals {
                    res_set.insert(priv_val);
                }
            } else {
                res_set.insert(*vid);
            }
        }
    }
    let mut cur_entropy = 0;
    // size of res
    let mut bitsize = 0;
    match blackbox_function{
        // just the entropy of key 
        BlackBoxFunc::AES128Encrypt => {
            return (vinfo_vec[2].entropy,Some(res_set));
        }
        // just the entropy of inputs (or + hash_values for Sha256Compression)
        BlackBoxFunc::Blake3 |
        BlackBoxFunc::Blake2s |
        BlackBoxFunc::Sha256Compression |
        BlackBoxFunc::Poseidon2Permutation |
        BlackBoxFunc::Keccakf1600 |
        BlackBoxFunc::MultiScalarMul | 
        BlackBoxFunc::EmbeddedCurveAdd => {
            cur_entropy = vinfo_vec.iter().map(|vi| vi.entropy).sum();
            bitsize = calculate_bitwidth(function.dfg.type_of_value(res_id));
            return (min(cur_entropy,bitsize),Some(res_set));
        }
        _ => {cur_entropy=0}

    }
    let mut sum_entropy_of_priv_vals = 0;
    for priv_id in &res_set {
        if let Some(info) = tags_map.get(priv_id) {
            sum_entropy_of_priv_vals += info.entropy;
        }
    }    
    if sum_entropy_of_priv_vals != 0 {
        return (min(sum_entropy_of_priv_vals,min(bitsize,cur_entropy)),Some(res_set))
    } else {
        return (min(bitsize ,cur_entropy),Some(res_set))
    }
}

// analytic formula for estimating max unique division results
// C/smth can have no more then 2*sqrt(C) + 1 unqie results
fn unique_division_results(c: u128, bit_width: u32) -> u64 {
    if c == 0 {
        return 0;
    }
    let possible_max = (2u32).pow(bit_width)-1 ;
    let sqrt_c = (c as f64).sqrt() as u128;
    let estimated = 2 * sqrt_c + 1;
    let max_unique = min(estimated, possible_max as u128);
    if max_unique <= 1 {
        0
    } else {
        max_unique.ilog2() as u64
    }
}


// function that calculates entropy (actually smth more kinda brute force work)
// of result of the instruction based on operands entropy
fn calculate_entropy (
    function: &Function,
    res_id: ValueId,
    instruction: &Instruction,
    vinfo_vec: &Vec<&ValueInfo>, 
    ids_vec: &Vec<ValueId>,
    tags_map: &BTreeMap<ValueId,ValueInfo>,
) -> (u64, Option<HashSet<ValueId>>){     
    let mut res_set = HashSet::<ValueId>::new();
    for (arg, vid) in vinfo_vec.iter().zip(ids_vec) {
        if arg.vis == Visibility::Private {

            if let Some(priv_vals) = arg.priv_vals.as_ref() {
                for &priv_val in priv_vals {
                    res_set.insert(priv_val);
                }
            } else {
                res_set.insert(*vid);
            }
        }
    }
    let mut cur_entropy = 0;
    // size of res
    let mut bitsize: u64 = 0;
    match instruction {
        Instruction::Binary(_binary) => {
            bitsize = function.dfg.get_value_max_num_bits(res_id) as u64;
            // H = min(sum of entropies of priv vals, current entropy, max bit width of the res) 
            match _binary.operator {
                // that ops are kinda obvious H = H1 + H2
                // for lt and eq it is work because of final formula 
                BinaryOp::Eq |
                BinaryOp::Lt |
                BinaryOp::Xor  => {
                    cur_entropy = vinfo_vec[0].entropy + vinfo_vec[1].entropy
                }
                BinaryOp::Sub { unchecked } |
                BinaryOp::Add {unchecked} => {
                    if unchecked == false {
                        let c0 = function.dfg.get_integer_constant(ids_vec[0]);
                        let c1 = function.dfg.get_integer_constant(ids_vec[1]);
                        // for fields and huge vals
                        let max_possible_val = if bitsize >= 128 {
                            u128::MAX 
                        } else {
                            1u128 << bitsize
                        };
                        cur_entropy = match (c0, c1) {
                            (Some(con), None) => {
                               let val = match con { IntegerConstant::Signed { value, .. } => value.abs() as u128, IntegerConstant::Unsigned { value, .. } => value };
                               min(vinfo_vec[1].entropy,(max_possible_val - val).ilog2() as u64) 
                            }
                            (None, Some(con)) => {
                               let val = match con { IntegerConstant::Signed { value, .. } => value.abs() as u128, IntegerConstant::Unsigned { value, .. } => value };
                               min(vinfo_vec[0].entropy,(max_possible_val-val).ilog2() as u64) 
                            }
                            _ =>  vinfo_vec[0].entropy + vinfo_vec[1].entropy
                        };
                    } else {
                        cur_entropy = vinfo_vec[0].entropy + vinfo_vec[1].entropy
                    }
                }
                BinaryOp::Mul { unchecked } => {
                    if unchecked == false {
                        let c0 = function.dfg.get_integer_constant(ids_vec[0]);
                        let c1 = function.dfg.get_integer_constant(ids_vec[1]);
                        // for fields and huge vals
                        let max_possible_val = if bitsize >= 128 {
                            u128::MAX 
                        } else {
                            1u128 << bitsize
                        };
                        cur_entropy = match (c0, c1) {
                            (Some(con), None) => {
                               let val = match con { IntegerConstant::Signed { value, .. } => value.abs() as u128, IntegerConstant::Unsigned { value, .. } => value };
                               min(vinfo_vec[1].entropy,((max_possible_val - 1)/val + 1).ilog2() as u64) 
                            }
                            (None, Some(con)) => {
                               let val = match con { IntegerConstant::Signed { value, .. } => value.abs() as u128, IntegerConstant::Unsigned { value, .. } => value };
                               min(vinfo_vec[0].entropy,((max_possible_val-1)/val + 1).ilog2() as u64) 
                            }
                            _ =>  vinfo_vec[0].entropy + vinfo_vec[1].entropy
                        };
                    } else {
                        cur_entropy = vinfo_vec[0].entropy + vinfo_vec[1].entropy
                    }
                }
                // if we know that one of the operands is constant then 
                // we know that the result is limited by that mask
                // both private => H = H1 + H2
                // if we have one constant => H = min(Hpriv,num of ones in constant) constant is
                // like filter, but also we can have entropy less than mask
                // if we have public var then we cannot guarantee that the result will not be
                // very small => consider it is equal to 0
                BinaryOp::And => {

                    if vinfo_vec[0].vis == Visibility::Private && vinfo_vec[1].vis == Visibility::Private {
                        cur_entropy = vinfo_vec[0].entropy + vinfo_vec[1].entropy
                    } else {
                        let c0 = function.dfg.get_integer_constant(ids_vec[0]);
                        let c1 = function.dfg.get_integer_constant(ids_vec[1]);

                        cur_entropy = match (c0, c1) {
                            (Some(con), None) => {
                                let val_ones = match con { IntegerConstant::Signed { value, .. } => value.count_ones(), IntegerConstant::Unsigned { value, .. } => value.count_ones() };
                                min(vinfo_vec[1].entropy, val_ones as u64)
                            }
                            (None, Some(con)) => {
                                let val_ones = match con { IntegerConstant::Signed { value, .. } => value.count_ones(), IntegerConstant::Unsigned { value, .. } => value.count_ones() };
                                min(vinfo_vec[0].entropy, val_ones as u64)
                            }
                            _ => 0
                        };
                    }
                }

                // both priv -> H1+H2
                // sec/Const -> min(Hsec, bitwidth - log2(C)) because of reducing amount of variants
                // Const/sec -> min(Hsec,log2(possible division results)) 
                // if we got one public then we cannot say what entropy the result will have so we
                // consider it is equal to zero
                BinaryOp::Div => {
                    if vinfo_vec[0].vis == Visibility::Private && vinfo_vec[1].vis == Visibility::Private {
                        cur_entropy = vinfo_vec[0].entropy + vinfo_vec[1].entropy
                    } else {
                        
                        let c0 = function.dfg.get_integer_constant(ids_vec[0]);
                        let c1 = function.dfg.get_integer_constant(ids_vec[1]);

                        cur_entropy = match (c0, c1) {
                            (Some(con), None) => {
                                let val = match con { IntegerConstant::Signed { value, .. } => value.abs() as u128, IntegerConstant::Unsigned { value, .. } => value };
                                let log = unique_division_results(val, calculate_bitwidth(function.dfg.type_of_value(ids_vec[1])) as u32);
                                min(vinfo_vec[1].entropy, log)
                            }
                            (None, Some(con)) => {
                                let val = match con { IntegerConstant::Signed { value, .. } => value.abs() as u128, IntegerConstant::Unsigned { value, .. } => value };
                                let log = if val <= 1 {
                                    0
                                } else {
                                    (val - 1).ilog2() + 1
                                };

                                // min(bitwidth - log, entropy)
                                min(calculate_bitwidth(function.dfg.type_of_value(res_id)).saturating_sub(log as u64), vinfo_vec[0].entropy)
                            }
                            _ => 0
                        }
                    }

                }
                // both priv -> H1+H2
                // sec%Const -> min(Hsec , log2(C)
                // Const%sec -> min(Hsec , log2(C)
                // because the result entropy cannot be more than one of the operadns
                // if we got one public then we cannot say what entropy the result will have so we
                // consider it is equal to zero
                BinaryOp::Mod => {
                    if vinfo_vec[0].vis == Visibility::Private && vinfo_vec[1].vis == Visibility::Private {
                        cur_entropy = min(vinfo_vec[0].entropy,vinfo_vec[1].entropy);
                    } else {
                        
                        let c0 = function.dfg.get_integer_constant(ids_vec[0]);
                        let c1 = function.dfg.get_integer_constant(ids_vec[1]);

                        cur_entropy = match (c0, c1) {
                            (Some(con), None) => {
                                let log = match con { IntegerConstant::Signed { value, .. } => value.abs().ilog2(), IntegerConstant::Unsigned { value, .. } => value.ilog2() };
                                min(vinfo_vec[1].entropy, log as u64)
                            }
                            (None, Some(con)) => {
                                let log = match con { IntegerConstant::Signed { value, .. } => value.abs().ilog2(), IntegerConstant::Unsigned { value, .. } => value.ilog2()};
                                min(vinfo_vec[0].entropy, log as u64)
                            }
                            _ => 0
                        }
                    }
                }
                BinaryOp::Shr |
                BinaryOp::Shl => {

                    // min(ent0, log2(bitwidth))
                    if vinfo_vec[0].vis == Visibility::Private && vinfo_vec[1].vis == Visibility::Private {
                        cur_entropy = min(vinfo_vec[0].entropy, calculate_bitwidth(function.dfg.type_of_value(ids_vec[1])).ilog2() as u64);
                    } else {
                        
                        let c0 = function.dfg.get_integer_constant(ids_vec[0]);
                        let c1 = function.dfg.get_integer_constant(ids_vec[1]);

                        // if C <</>> secret then (ent, num of variants)
                        // if secret <</>> C then min(entropty,bitw - shift) 
                        cur_entropy = match (c0, c1) {
                            (None, Some(con)) => {
                                let val = match con { IntegerConstant::Signed { value, .. } => value.abs() as u128, IntegerConstant::Unsigned { value, .. } => value};
                                // min(entropy,bitwidth - shift)
                                vinfo_vec[0].entropy.saturating_sub(val as u64)
                            }
                            (Some(_con),None) => {
                                //min(entropy, num of variants)
                                vinfo_vec[1].entropy
                            }
                            // else cases -> 0 because of the same "issue"
                            _ => 0
                        }
                    }
                }
                // or is also working like mask ()
                BinaryOp::Or => {
                    if vinfo_vec[0].vis == Visibility::Private && vinfo_vec[1].vis == Visibility::Private {
                        cur_entropy = vinfo_vec[0].entropy + vinfo_vec[1].entropy;
                    } else {
                        
                        let c0 = function.dfg.get_integer_constant(ids_vec[0]);
                        let c1 = function.dfg.get_integer_constant(ids_vec[1]);

                        // if C >> secret then 0
                        // if secret >> C then H = Hres - C
                        cur_entropy = match (c0, c1) {
                            (Some(con), None) => {
                                let val_ones = match con { IntegerConstant::Signed { value, .. } => value.count_ones(), IntegerConstant::Unsigned { value, .. } => value.count_ones() };
                                vinfo_vec[1].entropy.saturating_sub(val_ones as u64)
                            }
                            (None, Some(con)) => {
                                let val_ones = match con { IntegerConstant::Signed { value, .. } => value.count_ones(), IntegerConstant::Unsigned { value, .. } => value.count_ones() };
                                vinfo_vec[0].entropy.saturating_sub(val_ones as u64)
                            }
                            _ => 0
                        }
                    }
                }
            }
        },
        Instruction::Truncate { value: _, bit_size, ..} => {
            cur_entropy = vinfo_vec[0].entropy;
            bitsize = *bit_size as u64;
        }
        Instruction::Not (..) |
        Instruction::Cast (..)=> {
            cur_entropy = vinfo_vec[0].entropy;
            bitsize = function.dfg.get_value_max_num_bits(res_id) as u64;
        }
        Instruction::ArrayGet { array, index: _ } => {
            bitsize = function.dfg.get_value_max_num_bits(res_id) as u64;
            let (el_bit_width,len) = match function.dfg.type_of_value(*array) {
                ssa_Type::Array(types,len ) => {
                    (types[0].bit_size() as u64,len as u64)
                },
                // cannot happen
                _ => {(0,0)}
            };
            let log2_len = len.ilog2() as u64;
            let min_ent_idx = min(log2_len,vinfo_vec[1].entropy);
            let min_ent = min(el_bit_width,vinfo_vec[0].entropy);
            cur_entropy = match (vinfo_vec[0].vis,vinfo_vec[1].vis) {
                // add min(vec entropy, smth)
                (Visibility::Private, Visibility::Public) |
                (Visibility::Private, Visibility::Private)=> el_bit_width,
                (Visibility::Public, Visibility::Private) => min_ent_idx,
                _ => 0
            };

        }
        // in the worst case res entropy decreases on bitwidth of element minus value entropy
        Instruction::ArraySet { array, index: _, ..} => {
            bitsize = calculate_bitwidth(function.dfg.type_of_value(res_id));
            let (el_bit_width,len) = match function.dfg.type_of_value(*array) {
                ssa_Type::Array(types,len ) => {
                    (types[0].bit_size() as u64,len as u64)
                },
                // cannot happen
                _ => {(0,0)}
            };
            if vinfo_vec[2].entropy > vinfo_vec[0].entropy {cur_entropy = vinfo_vec[2].entropy}
            else {cur_entropy = vinfo_vec[0].entropy - el_bit_width + vinfo_vec[2].entropy}

        }
        Instruction::MakeArray {elements, typ: _} => {
            // ...
            bitsize = (elements.len() as u64) * (function.dfg.type_of_value(elements[0]).bit_size() as u64);
            for el in vinfo_vec{
                cur_entropy += el.entropy;
            }
        }
        _ => {}
    }
    let mut sum_entropy_of_priv_vals = 0;
    for priv_id in &res_set {
        if let Some(info) = tags_map.get(priv_id) {
            sum_entropy_of_priv_vals += info.entropy;
        }
    }    
    if sum_entropy_of_priv_vals != 0 {
        return (min(sum_entropy_of_priv_vals,min(bitsize,cur_entropy)),Some(res_set))
    } else {
        return (min(bitsize,cur_entropy),Some(res_set))
    }
}

// go through tags_map and search instructions that cause
// data leak through public return value
// bool return is representing deadend
fn tags_map_analysis (
    tags_map: &BTreeMap<ValueId,ValueInfo>,
    ret_value: ValueId,
    bad_instructions: &mut Vec<InstructionId>,
    function: &Function,
) -> bool {
    let _tag = tags_map.get(&ret_value).unwrap(); 
    let instruction_id = tags_map.get(&ret_value).unwrap().instr; 
    if instruction_id.is_some(){
        bad_instructions.push(instruction_id.unwrap());
        function.dfg[instruction_id.unwrap()].for_each_value(|value_id| {
            if tags_map.get(&value_id).is_some() && tags_map.get(&value_id).unwrap().vis == Visibility::Private   {
                tags_map_analysis(tags_map, value_id, bad_instructions, function);
            } 
        });
        return false;
    } else {
        return true;
    }
 
}


// only for debug purposes
fn tags_map_pretty_printer(
    tags_map: &BTreeMap<ValueId,ValueInfo>,
    function: &Function,
){
    println!("============TAGS MAP==============");
    for tag in tags_map{
        if tag.1.vis != Visibility::Private {
            println!("{} - {:?} - {} - {} - {:?}", tag.0, function.dfg.type_of_value((*tag.0).clone()),tag.1.vis, tag.1.entropy,tag.1.priv_vals);
        } else {
            println!("{} - {:?} - priv - {} - {:?}", tag.0, function.dfg.type_of_value((*tag.0).clone()),tag.1.entropy,tag.1.priv_vals);
        }
    }
}
