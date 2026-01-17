use acvm::acir::circuit::black_box_functions::BlackBoxFunc;
use crate::errors::{InternalBug, SsaReport};
use crate::ssa::ir::basic_block::BasicBlockId;
use crate::ssa::ir::function::Function;
use crate::ssa::ir::instruction::{Instruction, Intrinsic};
use crate::ssa::ir::value::ValueId;
use crate::ssa::ir::value::Value;
use crate::ssa::ssa_gen::Ssa;
use crate::ssa::Visibility; //NOTE: mb shoul use frontend::shared:visibility
use noirc_frontend::hir_def::types::Type;
use noirc_frontend::hir_def::function::FunctionSignature;
use std::collections::BTreeMap;

impl Ssa{

    pub(crate) fn check_for_data_leakage(
        &mut self,
    ) -> Vec<SsaReport>{
        // TODO: make correct processing of optional value
        // if self.function_signatures.is_none() {
        //     std::process::exit(1);
        // }
        let func_sigs = &self.function_signatures.clone().unwrap();
        println!("dbg print: ssa in cfdl {}\n", self);
        println!("signatures in check_for_data_leakage dbg print {:?}\n",func_sigs);
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

fn check_for_data_leakage_within_function(
    function: &Function,
    func_sig: &FunctionSignature,
) -> Vec<SsaReport> {

    let mut warnings: Vec<SsaReport> = Vec::new();

    let tags_map = make_tags_map(function, function.entry_block(), func_sig);
    tags_map_pretty_printer(&tags_map, function);
    println!("function returns {:?}\n",function.returns());

    let instructions = function.dfg[function.entry_block()].instructions();
    println!("dbg print: instructions {:?}",instructions);
    let mut flag = false;
    // TODO: 1) fix multiple warnings without flag
    // 2) add assert instruction analysis 
    // 3) handle case when return value is none 
    // WARN: something may go wrong because of the unwrap (if function returns nothing, should test)
    //  removed function.dfg.resolve and made it straightforward
    //  when i incorrectly use poseidon permutations function return of main is none
    //  and i get panic 
    for ret_val in function.returns().unwrap().iter(){
        if function.dfg.get_numeric_constant(*ret_val).is_some(){
            continue;
        }
        else if *(tags_map.get(ret_val).expect("error occured, there is no value in tags map with such id")) == Visibility::Private{
            flag = true;
            for instruction in instructions.iter(){
                for value_id in function.dfg.instruction_results(*instruction).iter() {
                    // NOTE: there was function.dfg.resolve
                    if *ret_val == *value_id{
                        // println!("dbg print: instruntion: {:?} and call stack {:?} \n", instruction, function.dfg.get_instruction_call_stack(*instruction));
                        // println!("dbg print: value: {:?} and value call stack {:?} \n", ret_val, function.dfg.get_value_call_stack(*ret_val));
                        let call_stack = function.dfg.get_instruction_call_stack(*instruction);
                        // BUG: makearray instruction hasn't call stack 
                        // fn main(x: u16) -> pub [u16; 5] {
                        //     let arr = [x;5];
                        //     arr
                        // }
                        // so i added is_empty
                        if call_stack.is_empty() {continue;}
                        warnings.push(SsaReport::Bug(InternalBug::DataLeak {
                            call_stack: call_stack,
                        }));
                    }
                }
            }
        }
    }
    // NOTE: this is for adding call stack of terminator instruction
    if flag{
        warnings.push(SsaReport::Bug(InternalBug::DataLeak {
            call_stack: function.dfg.get_call_stack(function.dfg[function.entry_block()].terminator().unwrap().call_stack())
        }));
    }
    warnings
}



// analyse instruction and set a tag to result value, add tag in variable tags map
//todo: think about efficiency and difference between vec and btreeset in this case
fn add_result_tag(
    function: &Function,
    instruction: &Instruction,
    tags_map: &mut BTreeMap<ValueId,Visibility>,
    ids_vec: &mut Vec<ValueId>,
){
    match *instruction{
        Instruction::Binary(..) => {
            //debug printers
            println!("{:?}",*instruction);
            println!("{:?}",ids_vec);
            let arg1 = ids_vec[0];
            let arg2 = ids_vec[1];
            let res = ids_vec[2];
            if function.dfg.get_numeric_constant(arg1).is_some(){
                tags_map.insert(arg1, Visibility::Public);
            }
            if function.dfg.get_numeric_constant(arg2).is_some(){
                tags_map.insert(arg2, Visibility::Public);
            }
            let tag1 = tags_map.get(&arg1).unwrap();
            let tag2 = tags_map.get(&arg2).unwrap();
            if *tag1 == Visibility::Private || *tag2 == Visibility::Private{
                tags_map.insert(res, Visibility::Private);
            } else {
                tags_map.insert(res,Visibility::Public);
            }
        },
        Instruction::Cast(..)
        | Instruction::Not(..)
        | Instruction::Truncate { .. } => {
            println!("{:?}",*instruction);
            println!("{:?}",ids_vec);
            let arg = ids_vec[0];
            if function.dfg.get_numeric_constant(arg).is_some(){
                tags_map.insert(arg, Visibility::Public);
            }
            let res = ids_vec[1];
            let tag = tags_map.get(&arg).unwrap();
            tags_map.insert(res, *tag);
        },
        Instruction::ArrayGet { .. } => {
            println!("{:?}",*instruction);
            println!("{:?}",ids_vec);
            let arr = ids_vec[0];
            let _ind = ids_vec[1];
            if function.dfg.get_numeric_constant(_ind).is_some() {
                tags_map.insert(_ind, Visibility::Public);
            }
            let res = ids_vec[2];
            let tag = tags_map.get(&arr).unwrap();
            tags_map.insert(res,*tag);
        },
        Instruction::MakeArray { .. } => {
            println!("{:?}",*instruction);
            println!("{:?}",ids_vec);
            let mut vis = Visibility::Public;
            for element in &ids_vec[0..ids_vec.len()-1] {
                println!("dbg print in makearray element: {} - {:?}",element,function.dfg.type_of_value(*element));
                if tags_map.get(element).is_none() {
                   if function.dfg.get_numeric_constant(*element).is_some() {
                        tags_map.insert(*element,Visibility::Public);
                    } 
                } else {
                    if *tags_map.get(element).unwrap() == Visibility::Private {
                        vis = Visibility::Private;
                    }
                }
            }
            tags_map.insert(ids_vec[ids_vec.len()-1], vis);
        }
        Instruction::Call { .. } => {
            println!("{:?}",*instruction);
            println!("{:?}",ids_vec);
            let function_value = &function.dfg[ids_vec[0]];
            println!("dbg print function value: {:?}\n", function_value);
            match function_value {
                Value::Intrinsic (intrinsic) => {
                    println!("dbg print intrinsic {:?}\n", intrinsic);
                    match intrinsic {
                        Intrinsic::BlackBox( blackbox_func ) => {
                            println!("dbg print: ids vec in call instruction {:?} \n", ids_vec);     
                            let ids_vec_len = ids_vec.len();
                            let tag = blackbox_function_analysis(function,blackbox_func, &ids_vec[1..ids_vec_len-1], tags_map);
                            tags_map.insert(ids_vec[ids_vec.len()-1],tag);
                        },
                       _ => {
                            println!("there is not bbox intrinsic function ")

                       }
                    }
                },
                _ => {
                    println!("value of function nor intrinsic \n");
                }
                
            }
            
        }
        _ => {
            println!("{:?} \n",*instruction);
            println!("{:?} \n",ids_vec);
        }
    }
}

///add main function arguments in tags_map base on their visibility
fn add_main_args_in_tags_map(
    tags_map: &mut BTreeMap<ValueId,Visibility>,
    func_sig: &FunctionSignature,
    function: &Function,
){

    let mut args= Vec::new();

    // TODO: cover all cases
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

    println!("dbg print args vector {:?}\n",args);

    for (metadata,id) in (args).iter().zip(function.parameters()){
        tags_map.insert(*id,metadata.0);
    }
}

// Go through each instruction in the block and marking all variables
fn make_tags_map(
    function: &Function,
    block: BasicBlockId,
    func_sig: &FunctionSignature,
) -> BTreeMap<ValueId, Visibility>{
    let instructions = function.dfg[block].instructions();

    let mut tags:BTreeMap<ValueId, Visibility> = BTreeMap::new();

    add_main_args_in_tags_map(&mut tags, func_sig,function);

    println!("dbg print block\n {:?}\n",block);
    println!("dbg print instructions\n {:?}\n",instructions);

    for instruction in instructions.iter() {
        let mut instruction_arguments_and_results = Vec::new();
        println!("instruction: {:?}", instruction);
        // Insert all instruction arguments
        println!("========instruction arguments=======");
        function.dfg[*instruction].for_each_value(|value_id| {
        // NOTE: there was function.dfg.resolve
            println!("{} - {:?}", value_id, function.dfg.type_of_value(value_id));
            instruction_arguments_and_results.push(value_id); 
        });
        // And all results
        // println!("instruction results ");
        for value_id in function.dfg.instruction_results(*instruction).iter() {
        // NOTE: there was function.dfg.resolve
            println!("instruction result {} - {:?}", *value_id, function.dfg.type_of_value(*value_id));
            instruction_arguments_and_results.push(*value_id);
        }

        let mut instruction_arguments_and_results_copy = instruction_arguments_and_results.clone();

        add_result_tag(function,&function.dfg[*instruction],&mut tags, &mut instruction_arguments_and_results_copy);

    }

    tags

}

fn blackbox_function_analysis(
    function: &Function,
    blackbox_function: &BlackBoxFunc,
    arguments: &[ValueId],
    tags_map: &mut BTreeMap<ValueId, Visibility>,
) -> Visibility{
   match blackbox_function {
        // TODO: external safety check for non valid prog design
        // for example iv private, key is public 
        BlackBoxFunc::AES128Encrypt => {
            println!("dbg print: arguments of blackbox function\n {:?}", arguments);
            let _input = arguments[0];
            let _iv = arguments[1];
            let key = arguments[2];
            if function.dfg.get_numeric_constant(key).is_some(){
                tags_map.insert(key, Visibility::Public);
            }
            if *tags_map.get(&key).unwrap() == Visibility::Public {
                return Visibility::Private
            } else {
                return Visibility::Public
            } 
        },
        // TODO: keccak poseidon
        BlackBoxFunc::Blake3 |
        BlackBoxFunc::Blake2s |
        BlackBoxFunc::Sha256Compression |
        // NOTE: keccak and poseidon are inreversible 
        BlackBoxFunc::Keccakf1600 |
        BlackBoxFunc::Poseidon2Permutation => {
            // TODO: use entropy analyzer in far future
            return Visibility::Public
        },
        // NOTE: very primitive logic (if smth is private then result is private)
        // TODO: handle all cases when implement a more detailed version
        BlackBoxFunc::EmbeddedCurveAdd => {
            // NOTE: dont know anything about pedantic solving flag
            // but since it is numeric constant then it does not affect on result visibility
            for arg in arguments.iter() {
                if function.dfg.get_numeric_constant(*arg).is_some() {
                    tags_map.insert(*arg, Visibility::Public);
                } else {
                    if *tags_map.get(arg).unwrap() == Visibility::Private {return Visibility::Private;}
                }
            }
            return Visibility::Public;
        },
        // NOTE: scalar is public -> depends on points visibility
        // scalar is private -> public (discrete logarithm problem)
        BlackBoxFunc::MultiScalarMul => {
            let points = arguments[0];
            let scalars = arguments[1];
            if *tags_map.get(&scalars).unwrap() == Visibility::Private { return Visibility::Public }
            return *tags_map.get(&points).unwrap()
        },
        // NOTE: logic is that parametrs of function 
        // dont compromise anything (since key is public, hash is hash
        // and signature is signature)
        BlackBoxFunc::EcdsaSecp256k1 |
        BlackBoxFunc::EcdsaSecp256r1 => {
            return Visibility::Public;
        }

        _ => {
            println!("other bbox functions");
            return Visibility::Public
        }
    }
}


// only for debug purposes
fn tags_map_pretty_printer(
    tags_map: &BTreeMap<ValueId,Visibility>,
    function: &Function,
){
    println!("============TAGS MAP==============");
    for tag in tags_map{
        if *tag.1 != Visibility::Private {
            println!("{} - {:?} - {}", tag.0, function.dfg.type_of_value((*tag.0).clone()),tag.1);
        } else {
            println!("{} - {:?} - priv", tag.0, function.dfg.type_of_value((*tag.0).clone()));
        }
    }
}
