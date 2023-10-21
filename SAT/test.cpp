import Algo;
import Algo2;
import <filesystem>;
template <class T>
concept equality_comparable = requires(T a, T b) {
  a == b;
};

static int number_of_tests;
static int number_of_passed;
static int number_of_failed;

template <equality_comparable T>
bool compare(T Lhs, T Rhs, size_t Line, const char Filename[], const char Functionname[]) {
  number_of_tests++;
  if (Lhs == Rhs) {
    number_of_passed++;
    //std::cout << "\033[1;32mPASSED!\033[0m\n";
    return true;
  }
  number_of_failed++;
  std::cout << "\033[1;31mTEST \"" << Functionname << "\" FAILED!\n";
  std::cout << "Where: " << Filename << ":" << Line << std::endl;
  std::cout << "\033[1;34mLhs: " << Lhs << "\nRhs: " << Rhs << "\033[0m"
            << std::endl;
  return false;
}
template <equality_comparable T>
bool compare(T Lhs, T Rhs, std::string ErrMessage, size_t Line, const char Filename[], const char Functionname[]) {
  number_of_tests++;
  if (Lhs == Rhs) {
    number_of_passed++;
    //std::cout << "\033[1;32mPASSED!\033[0m\n";
    return true;
  }
  number_of_failed++;
  std::cout << "\033[1;31mTEST \"" << Functionname << "\" FAILED!\n";
  std::cout << "Where: " << Filename << ":" << Line << std::endl;
  std::cout << "\033[1;34mLhs: " << Lhs << "\nRhs: " << Rhs << "\033[0m"
            << std::endl;
  std::cout << "\033[1;33m"+ErrMessage << std::endl;
  return false;
}

bool compare(bool Cmp, size_t Line, const char Filename[], const char Functionname[]) {
  number_of_tests++;
  if (Cmp) {
    number_of_passed++;
    //std::cout << "\033[1;32mPASSED!\033[0m\n";
    return true;
  }
  number_of_failed++;
  std::cout << "\033[1;31mTEST \"" << Functionname << "\" FAILED!\n";
  std::cout << "Where: " << Filename << ":" << Line << std::endl;
  return false;
}

#define EXPECT_EQ_MSG(lhs, rhs, ErrMessage) compare(lhs, rhs, ErrMessage, __LINE__, __FILE__, __FUNCTION__)
#define EXPECT_EQ(lhs, rhs) compare(lhs, rhs, __LINE__, __FILE__, __FUNCTION__)
#define EXPECT_SET(cmp) compare(cmp, __LINE__, __FILE__, __FUNCTION__)

void summary() {
  std::cout << "\n\033[1;34mSUMMARY:\n";
  if (number_of_failed > 0)
    std::cout << "\033[1;31m[" << number_of_failed << "/" <<number_of_tests<< "] TESTS FAILED\n";
  if (number_of_passed > 0)
    std::cout << "\033[1;32m[" << number_of_passed << "/" <<number_of_tests<< "] TESTS PASSED\n";
}

void testSetVar() {
  Sat::Sat_t Sat({{1, 2, -3}, {-1, 2}});
  // ( x1 | x2 | ~x3 ) & ( ~x1 | x2 )

  auto Output = Sat.setVar(-1);
  EXPECT_EQ(Output.dumpStr(), std::string("( x2 | ~x3 )"));
  Output = Sat.setVar(1);
  EXPECT_EQ(Output.dumpStr(), std::string("( x2 )"));
  Output = Sat.setVar(2);
  EXPECT_EQ(Output.dumpStr(), std::string(""));
  Output = Sat.setVar(3);
  EXPECT_EQ(Output.dumpStr(), std::string("( x1 | x2 ) & ( ~x1 | x2 )"));
}

void testSimplestCheck() {
  Sat::Sat_t SatTrue({{1, 2, -3}, {-1, 2}});
  Sat::Sat_t SatFalse({{1}, {-1}});
  // ( x1 | x2 | ~x3 ) & ( ~x1 | x2 )

  EXPECT_EQ(Algo::simplestCheck(SatTrue, 3), true);
  EXPECT_EQ(Algo::simplestCheck(SatFalse, 1), false);
}

void testFileInput() {
  Sat::Sat_t SatTrue = Sat::inputFromFile("cnf/manual.cnf");
  Sat2::Sat_t SatTrue2 = Sat2::inputFromFile("cnf/manual.cnf");
  EXPECT_EQ(SatTrue.dumpStr(), std::string("( x1 | x2 | ~x3 ) & ( ~x1 | x2 )"));
  EXPECT_EQ(Algo::simplestCheck(SatTrue, 3), true);
  EXPECT_EQ(SatTrue2.dumpStr(), std::string("( x1 | x2 | ~x3 ) & ( ~x1 | x2 )"));
  EXPECT_EQ(Algo2::simplestCheck(SatTrue2, 3), true);
}

void testUf() {
  std::string path = "./cnf";
  for (const auto & entry : std::filesystem::directory_iterator(path)) {
    Sat::Sat_t SatTrue = Sat::inputFromFile(entry.path());
    Sat2::Sat_t SatTrue2 = Sat2::inputFromFile(entry.path());
    EXPECT_EQ_MSG(SatTrue.dumpStr(), SatTrue2.dumpStr(), std::string(entry.path()) + " input differs in Sat and Sat2");

    EXPECT_EQ_MSG(Algo::simplestCheck(SatTrue, 3), true, std::string(entry.path()) + " should be SAT, but Algo::simplestCheck says UNSAT");
    EXPECT_EQ_MSG(Algo2::simplestCheck(SatTrue2, 3), true, std::string(entry.path()) + " should be SAT, but Algo2::simplestCheck says UNSAT");
    
    auto Set1 = Algo::simplestFind<3>(SatTrue);
    auto Set2 = Algo2::simplestFind<3>(SatTrue2);

    EXPECT_EQ_MSG(Set1.has_value(), true, std::string(entry.path()) + " should be SAT, but Algo::simplestFind says UNSAT");
    EXPECT_EQ_MSG(Set2.has_value(), true, std::string(entry.path()) + " should be SAT, but Algo2::simplestFind says UNSAT");
    
    //SatTrue.dump();
    //SatTrue2.dump();
  }
}

void testSimplestFind() { // to implement
  Sat::Sat_t SatFalse({{1}, {-1}});
  auto SetFalse = Algo::simplestFind<1>(SatFalse);
  Sat::Sat_t Sat1({{1, 2, -3}, {-1, 2}});
  auto Set1 = Algo::simplestFind<3>(Sat1);
  Sat::Sat_t Sat2({{1, 2, -3}, {1, 2}});
  auto Set2 = Algo::simplestFind<3>(Sat2);

  EXPECT_EQ(SetFalse.has_value(), false);
  EXPECT_EQ(Set1.has_value(), true);
  EXPECT_EQ(*Set1, std::string("~x1 ~x2 ~x3 "));
  EXPECT_EQ(*Set2, std::string("x1 ~x2 ~x3 "));

  Sat::Sat_t Sat3({{1, -2}, {1, 2}});
  EXPECT_EQ(*Algo::simplestFind<2>(Sat3), std::string("x1 ~x2 "));
  Sat::Sat_t Sat4({{1, 2}, {-1, 2}});
  EXPECT_EQ(*Algo::simplestFind<2>(Sat4), std::string("~x1 x2 "));
}

void testSimplestFind2() { // to implement
  Sat2::Sat_t SatFalse({{1}, {-1}});
  auto SetFalse = Algo2::simplestFind<1>(SatFalse);
  EXPECT_EQ(SetFalse.has_value(), false);

  Sat2::Sat_t Sat1({{1, 2, -3}, {-1, 2}});
  auto Set1 = Algo2::simplestFind<3>(Sat1);
  EXPECT_EQ(Set1.has_value(), true);
  EXPECT_EQ(*Set1, std::string("~x1 ~x2 ~x3 "));

  Sat2::Sat_t Sat2({{1, 2, -3}, {1, 2}});
  auto Set2 = Algo2::simplestFind<3>(Sat2);
  EXPECT_EQ(*Set2, std::string("x1 ~x2 ~x3 "));

  Sat2::Sat_t Sat3({{1, -2}, {1, 2}});
  EXPECT_EQ(*Algo2::simplestFind<2>(Sat3), std::string("x1 ~x2 "));

  Sat2::Sat_t Sat4({{1, 2}, {-1, 2}});
  EXPECT_EQ(*Algo2::simplestFind<2>(Sat4), std::string("~x1 x2 "));
}

int main(int argc, char **argv) {
  testSetVar();
  testSimplestCheck();
  testSimplestFind();
  testSimplestFind2();
  testFileInput();
  testUf();

  summary();
}