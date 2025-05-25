struct student {
    pub deadline: u8,
    Lab: bool,
    smth: i32,
}

fn main(student: pub student, var: pub u32) -> pub student{
    let mut ME: student = student;
    ME.deadline += var as u8;
    ME
}
