use jcdc_decompiler::ClassOptions;
use jcdc_jvm::ClassPool;
use std::sync::Arc;

fn main() -> anyhow::Result<()> {
    let path = std::env::args().nth(1).unwrap();
    let pooldir = std::env::args().nth(2).unwrap_or_else(|| {
        std::path::Path::new(&path).parent().unwrap().to_string_lossy().to_string()
    });
    let data = std::fs::read(&path)?;
    let (_, cf) = jcdc_classfile::parse_classfile(&data).unwrap();
    let cp = jcdc_classfile::CpLookup::new(&cf.constant_pool);
    let name = cp.class_name(&cf.constant_pool, cf.this_class).unwrap().to_string();
    let pc = Arc::new(jcdc_jvm::PoolClass { internal_name: name, cf, cp });
    let pool = ClassPool::from_paths([pooldir.as_str()])?;
    let s = jcdc_decompiler::decompile_class(&pc, &pool, &ClassOptions::default())?;
    println!("{}", s.len());
    Ok(())
}
