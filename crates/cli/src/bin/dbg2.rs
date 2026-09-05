use jcdc_classfile::{parse_classfile, CpLookup};
use jcdc_jvm::{ClassPool, PoolClass};
use std::sync::Arc;

fn main() -> anyhow::Result<()> {
    let path = std::env::args().nth(1).unwrap();
    let want = std::env::args().nth(2).unwrap();
    let pooldir = std::env::args().nth(3).unwrap_or_else(|| {
        std::path::Path::new(&path).parent().unwrap().to_string_lossy().to_string()
    });
    let data = std::fs::read(&path)?;
    let (_, cf) = parse_classfile(&data).unwrap();
    let cp = CpLookup::new(&cf.constant_pool);
    let name = cp.class_name(&cf.constant_pool, cf.this_class).unwrap().to_string();
    let pc = Arc::new(PoolClass { internal_name: name, cf, cp });
    let pool = ClassPool::from_paths([pooldir.as_str()])?;
    let (want_name, want_nth) = match want.split_once('#') {
        Some((n, k)) => (n.to_string(), k.parse::<usize>().unwrap_or(0)),
        None => (want.clone(), 0),
    };
    let mut seen = 0usize;
    let mi = (0..pc.cf.methods.len())
        .find(|&i| {
            if pc.method_name(i) == Some(want_name.as_str()) {
                if seen == want_nth {
                    return true;
                }
                seen += 1;
            }
            false
        })
        .unwrap();
    match jcdc_decompiler::method::decompile_method(&pc, &pool, mi) {
        Ok(Some(mb)) => {
            if std::env::var("JCDC_PRINT").is_ok() {
                if std::env::var("JCDC_PRINT_TREE").is_ok() {
                    let d = format!("{:#?}", mb.body);
                    for l in d.lines() {
                        if l.contains("PreIncDec") || l.contains("While") || l.contains("Labeled") {
                            eprintln!("TREE: {}", l.trim());
                        }
                    }
                }
                let text = jcdc_decompiler::emit::Printer::new(&pc, &pool, &mb.vt)
                    .into_string(&mb.body);
                println!("{}", text);
            } else {
                println!("{:#?}", mb.body);
            }
        }
        Ok(None) => println!("no body"),
        Err(e) => println!("err {}", e),
    }
    Ok(())
}
