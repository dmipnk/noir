fn main(x: Field ) -> pub std::embedded_curve_ops::EmbeddedCurvePoint  {
    let point1 = std::embedded_curve_ops::EmbeddedCurvePoint { x: x, y: 2, is_infinite: false};
    let point2 = std::embedded_curve_ops::EmbeddedCurvePoint { x: 3, y: 4, is_infinite: false };
    let result = std::embedded_curve_ops::embedded_curve_add(point1, point2);
    result
}


