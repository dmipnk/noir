use crate::errors::{InternalBug, SsaReport};
use crate::ssa::ir::basic_block::BasicBlockId;
use crate::ssa::ir::function::Function;
use crate::ssa::ir::instruction::Instruction;
use crate::ssa::ir::value::ValueId;
use crate::ssa::ssa_gen::Ssa;
use noirc_frontend::ast::Visibility;
use noirc_frontend::hir_def::types::Type;
use noirc_frontend::hir_def::function::FunctionSignature;
use std::collections::{BTreeMap, BTreeSet};
use crate::ssa::checks::check_for_underconstrained_values::Context;

impl Ssa{

    pub(crate) fn check_for_data_leakage(
        &mut self,
        func_sigs: &Vec<FunctionSignature>,
    ) -> Vec<SsaReport>{
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

    let mut context = Context::default();
    let mut warnings: Vec<SsaReport> = Vec::new();

    let tags_map = context.make_tags_map(function, function.entry_block(), func_sig);
    println!("\ndbg print tags map in function {:?}", tags_map);
    println!("function returns {:?}\n",function.returns());

    let instructions = function.dfg[function.entry_block()].instructions();
    let mut flag = false;
    //todo: fix multiple warnings without flag
    for ret_val in function.returns().iter(){
        if *(tags_map.get(ret_val).expect("error occured, there is no value in tags map with such id")) == Visibility::Private{
            flag = true;
            for instruction in instructions.iter(){
                for value_id in function.dfg.instruction_results(*instruction).iter() {
                    if *ret_val == function.dfg.resolve(*value_id){
                        warnings.push(SsaReport::Bug(InternalBug::DataLeak {
                            call_stack: function.dfg.get_instruction_call_stack(
                                *instruction
                            ),
                        }));
                    }
                }
            }
        }
    }
    if flag{
        warnings.push(SsaReport::Bug(InternalBug::DataLeak {
            call_stack: function.dfg.get_call_stack(function.dfg[function.entry_block()].terminator().unwrap().call_stack())
        }));
    }
    warnings
}

impl Context{

    // analyse instruction and set a tag to result value, add tag in variable tags map
    fn add_result_tag(
        &mut self,
        function: &Function,
        instruction: &Instruction,
        tags_map: &mut BTreeMap<ValueId,Visibility>,
        ids_set: &mut BTreeSet<ValueId>,
    ){
        match *instruction{
            Instruction::Binary(..) => {
                //debug printers
                println!("{:?}",*instruction);
                println!("{:?}",ids_set);
                let arg1 = ids_set.pop_first().unwrap();
                let arg2 = ids_set.pop_first().unwrap();
                let res = ids_set.pop_first().unwrap();
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
                println!("{:?}",ids_set);
                let arg = ids_set.pop_first().unwrap();
                if function.dfg.get_numeric_constant(arg).is_some(){
                    tags_map.insert(arg, Visibility::Public);
                }
                let res = ids_set.pop_first().unwrap();
                let tag = tags_map.get(&arg).unwrap();
                tags_map.insert(res, *tag);
            },
            _ => {
                println!("{:?}",*instruction);
                println!("{:?}",ids_set);
            }
        }
    }

    ///add main function arguments in tags_map base on their visibility
    fn add_main_args_in_tags_map(
        &mut self,
        tags_map: &mut BTreeMap<ValueId,Visibility>,
        func_sig: &FunctionSignature,
        function: &Function,
    ){

        let mut args= Vec::new();

        //todo: cover all cases
        for param in &func_sig.0{
            match &param.1 {
                Type::DataType(definition, generics) => {
                    let fields = definition.borrow().get_fields(generics).unwrap();
                    for field in fields{
                        args.push((param.2, field.1));
                    }
                },
                _ => {args.push((param.2, (param.1).clone()))},
            }
        }

        println!("dbg print args vector {:?}",args);

        for (metadata,id) in (args).iter().zip(function.parameters()){
            tags_map.insert(*id,metadata.0);
        }
    }

    // Go through each instruction in the block and marking all variables
    fn make_tags_map(
        &mut self,
        function: &Function,
        block: BasicBlockId,
        func_sig: &FunctionSignature,
    ) -> BTreeMap<ValueId, Visibility>{
        let instructions = function.dfg[block].instructions();

        let mut tags:BTreeMap<ValueId, Visibility> = BTreeMap::new();

        self.add_main_args_in_tags_map(&mut tags, func_sig,function);

        println!("dbg print block\n {:?}\n",block);
        println!("dbg print instructions\n {:?}\n",instructions);

        for instruction in instructions.iter() {
            let mut instruction_arguments_and_results = BTreeSet::new();

            // Insert all instruction arguments
            function.dfg[*instruction].for_each_value(|value_id| {
                instruction_arguments_and_results.insert(function.dfg.resolve(value_id));
            });
            // And all results
            for value_id in function.dfg.instruction_results(*instruction).iter() {
                instruction_arguments_and_results.insert(function.dfg.resolve(*value_id));
            }

            let mut instruction_arguments_and_results_copy = instruction_arguments_and_results.clone();

            self.add_result_tag(function,&function.dfg[*instruction],&mut tags, &mut instruction_arguments_and_results_copy);

        }

        tags

    }

}