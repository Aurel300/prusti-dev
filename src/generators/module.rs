use std::collections::HashMap;
use module_tree::*;
use class_name::*;

pub fn generate_module(class_names: Vec<&ClassName>) -> String {
    let mut modules = ModuleTree::default();

    for class_name in class_names {
        let components: Vec<String> = class_name
            .full_rust_components()
            .iter()
            .map(|x| x.to_string())
            .collect();
        modules = modules.insert(components);
    }

    let modules_tree = modules
        .visit(|modules| {
            let modules: HashMap<String, Option<String>> = modules;
            let mut res: Vec<String> = vec![];
            for (name, opt_rec_result) in modules {
                match opt_rec_result {
                    None => {
                        res.push(format!("mod {}_wrapper;\n", name));
                        res.push(format!("pub use self::{}_wrapper::*;\n", name));
                    }
                    Some(rec_result) => {
                        res.push(format!("pub mod {} {{\n", name));
                        let code: String = rec_result.to_string();
                        res.push(code);
                        res.push(format!("}} // end of mod {}\n", name));
                    }
                }
            }
            res.join("")
        })
        .unwrap_or_else(|| "// No modules".to_string());

    vec![
        "//! Automatically generated code\n".to_string(),
        "#![allow(non_snake_case)]\n".to_string(),
        modules_tree,
    ].join("\n") + "\n"
}
