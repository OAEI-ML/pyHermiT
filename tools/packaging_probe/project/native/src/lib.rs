use pyo3::prelude::*;

#[pymodule]
fn _native(_module: &Bound<'_, PyModule>) -> PyResult<()> {
    Ok(())
}
