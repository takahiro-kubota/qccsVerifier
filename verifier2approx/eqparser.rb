# this is also the indis parser

require "envparser"

class EqParser < EnvParser
 class Equation
   def initialize
     @lhs = Environment.new
     @rhs = Environment.new
     @counter = 0
     @wrt = [] # of nat. symbs., only for ind. expr.
   end
   attr_accessor :lhs, :rhs, :counter, :wrt
 end

 def initialize
   @equations = Hash.new
 end
 attr_accessor :equations
 
 public
 def parse(equations, arg_nametable)
   equations.each{ |eq_name, eq_body0|
     equation = Equation.new

     # for indis
     if eq_body0[0] != nil
       equation.wrt << eq_body0[0]
     end
     #

     eq_body = eq_body0[1]
          
     nametable = arg_nametable.copy
     nametable.dsyms["__"] = true
     nametable.operators["__"] = true

     unless eq_body.include?("=") 
       raise "no = in equation:" + eq_body
     end
     unless (i = eq_body.index("=")) == eq_body.rindex("=")
       raise "= must occur only once:" + eq_body
     end
     lhs_string = eq_body[0 .. i - 1]
     rhs_string = eq_body[i + 1 .. eq_body.length]

     lhs_tree = __parse_inter(lhs_string)
     begin
       __qv_check(lhs_tree)
       __form_check(lhs_tree, nametable)
     end
     rhs_tree = __parse_inter(rhs_string)
     begin
       __qv_check(rhs_tree)
       __form_check(rhs_tree, nametable)
     end

     equation.lhs = lhs_tree.normalform
     equation.rhs = rhs_tree.normalform
     
     @equations[eq_name] = equation
   }
 end

 def show_all
   @equations.each{ |equation_name, equation|
     p "---begin equation:" + equation_name + "---"
     equation.lhs.show
     print "\n";
     equation.rhs.show
     p "---end equation:" + equation_name + "---"
   }
 end
end
