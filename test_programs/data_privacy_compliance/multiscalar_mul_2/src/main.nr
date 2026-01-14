fn main(point1: pub std::embedded_curve_ops::EmbeddedCurvePoint, point2: pub std::embedded_curve_ops::EmbeddedCurvePoint, scalars: pub [std::embedded_curve_ops::EmbeddedCurveScalar; 2]) -> pub std::embedded_curve_ops::EmbeddedCurvePoint{
    let result = std::embedded_curve_ops::multi_scalar_mul([point1, point2],scalars);
    result
}

