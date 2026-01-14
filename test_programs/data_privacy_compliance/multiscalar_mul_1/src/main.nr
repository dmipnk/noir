fn main(scalars: pub [std::embedded_curve_ops::EmbeddedCurveScalar; 2]) -> pub std::embedded_curve_ops::EmbeddedCurvePoint{
    let point1 = std::embedded_curve_ops::EmbeddedCurvePoint { x: 3, y: 2, is_infinite: true};
    let point2 = std::embedded_curve_ops::EmbeddedCurvePoint { x: 3, y: 4, is_infinite: false };
    let result = std::embedded_curve_ops::multi_scalar_mul([point1, point2],scalars);
    result
}

