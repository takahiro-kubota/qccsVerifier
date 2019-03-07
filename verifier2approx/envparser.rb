require "mylib"
require "environment"

class EnvParser
  class EnvParseTree
    class EnvParseTreeNode
      def initialize
        @kind = nil # "env_symbol", "oper", "tensor"
        @name = nil # name of env_symbol or oper, String
        @target = [] # Array of qvar
      end
      attr_accessor :kind, :name, :target
    end # class EnvParseTreeNode

    def initialize
      @node = EnvParseTreeNode.new
      @succ = Array.new
    end
    attr_accessor :node, :succ
    
    public
    def normalform
      def __scan_tree(env_parse_tree)
        ret = [[], []]
        ept_node = env_parse_tree.node
        case ept_node.kind
        when "env_symbol"
          ret[1] << Environment::EnvNode.new(ept_node.name, ept_node.target) #to syms
        when "oper"
          ret[0] << Environment::EnvNode.new(ept_node.name, ept_node.target) #to ops
        when "tensor"
          # do nothing
        else 
          raise "Invalid kind #{kind}"
        end
        env_parse_tree.succ.each { |succ_i|
          scanned_i = __scan_tree(succ_i)
          ret[0] |= scanned_i[0] # ops
          ret[1] |= scanned_i[1] # syms
        }
        
        ret
      end # __scan_tree

      ret = Environment.new
      scanned = __scan_tree(self)
      ret.ops = scanned[0]
      ret.syms = scanned[1].sort!
      ret 
    end
  end # class EnvParseTree

  def initialize
    @normalform_envs = Hash.new #H["env_name"] = Environment
    @parse_trees = Hash.new # for debug
  end
  attr_accessor :normalform_envs

  def __parse_inter(env)
    parse_tree = EnvParseTree.new
    node = EnvParser::EnvParseTree::EnvParseTreeNode.new
    succ = Array.new

    nest = 0
    head = 0
    tail = 0
    node_is_tensor = false

    i = 0
    env.each_char { |char|
      if char == "(" then
        nest += 1
      elsif char == ")" then
        nest -= 1
      elsif char == "*" and nest == 0 then
        node_is_tensor = true
        tail = i - 1
        succ.push(__parse_inter(env[head..tail]))
        head = i + 1
      end
      i += 1
    }

    if node_is_tensor == false then
      if (env_bra = env.index("(")) != nil then # operator
        # for node
        unless (qvars_bra = env.index("[")) and (qvars_ket = env.index("]"))
          raise "malformed operator app.: " + env
        end
        node.kind = "oper"
        node.name = env[0 .. qvars_bra-1]
        node.target = env[qvars_bra+1 .. qvars_ket-1].split(",")
        # for succ
        env_ket = env_bra + 1
        i = 0
        nest_bracket = 0
        env[env_bra+1 .. env.length-1].each_char{ |char|
          if char == "("
            nest_bracket += 1
          elsif char == ")"
            if nest_bracket == 0
              env_ket += i
              break
            end
            nest_bracket -= 1
          end
          i += 1
        }
        if env_ket == 0;
          raise "malformed operator app.:" + env
        end
        succ.push(__parse_inter(env[env_bra+1 .. env_ket-1]))
      else #env symbol
        unless (qvars_bra = env.index("[")) and (qvars_ket = env.index("]"))
          raise "malformed env symbol: " + env
        end
        node.kind = "env_symbol"
        node.name = env[0..qvars_bra-1]
        node.target = env[qvars_bra+1 .. qvars_ket-1].split(",")
      end
    else #node_is_tensor == true
      node.kind = "tensor"
      succ.push(__parse_inter(env[head..env.length-1]))
    end
    parse_tree.node = node
    parse_tree.succ = succ
    parse_tree
  end # def __parse_inter

  def __qv_check(parse_tree)
    ret = [] # Array of qvar
    kind = parse_tree.node.kind 
    case kind
    when "env_symbol"
      ret = parse_tree.node.target
    when "oper"
      ret = __qv_check(parse_tree.succ[0])
      unless parse_tree.node.target - ret == []
        raise "#{parse_tree.node.name}[#{parse_tree.node.target}] is performed to unexpected target #{ret}"
      end
    when "tensor"
      parse_tree.succ.each { |succ_i|
        qvars_i = __qv_check(succ_i)
        unless disjoint?(ret, qvars_i)
          raise "unique ownership is broken, #{ret}, #{qvars_i}"
        end
        ret |= qvars_i
      }
    else
      raise "Invalid kind #{kind}"
    end
    
    ret
  end #__qv_check

  def __form_check(parse_tree, nametable)
    kind = parse_tree.node.kind
    case kind
    when "env_symbol"
      if nametable.dsyms["__"] == true
        # do nothing
      elsif parse_tree.node.name == "__"
        raise "__ is not allowed for the name of density operator  #{parse_tree.node.name}"
      else
        unless (expected_type = nametable.dsyms[parse_tree.node.name])
          raise "undeclared density operator name #{parse_tree.node.name}"
        end
        target_type = []
        parse_tree.node.target.each { |qvar|
          target_type << nametable.qvars[qvar]
        }
        if target_type.compact == []
          # do nothing, its outsider's qvars that may be sent to unrestricted channel
        elsif target_type != expected_type
          raise "unexpected #{parse_tree.node.target}'s type #{target_type}, expected #{expected_type} for #{parse_tree.node.name}"
        end
      end
    when "oper"
      if parse_tree.node.name == "Tr" or nametable.operators["__"] == true
        #do nothing
      else
        unless nametable.operators[parse_tree.node.name]
          raise "undeclared operator name #{parse_tree.node.name}"
        end
        expected_type = nametable.operators[parse_tree.node.name].clone
        target_type = []
        exception_indices = []
        i = 0
        parse_tree.node.target.each { |qvar|
          if nametable.qvars[qvar] != nil
            target_type << nametable.qvars[qvar]
          else
            exception_indices << i
          end
          i += 1
        }
        exception_indices.each { |i|
          expected_type[i] = nil
        }
        expected_type.compact!
        unless target_type == expected_type
          raise "unexpected #{parse_tree.node.target}'s type #{target_type}, expected #{expected_type} for #{parse_tree.node.name}"
        end
      end
      begin
        __form_check(parse_tree.succ[0], nametable)
      end
    when "tensor"
      tmp_qvars = []
      parse_tree.succ.each { |succ_i|
        begin
          __form_check(succ_i, nametable)
        end
      }
    else
      raise "Invalid kind #{kind}"
    end
  end # def __form_check(parse_tree, nametable)

  public
  def parse_all(environments, nametable)
    environments.each{ |env_name, env_body|
      parse_tree = __parse_inter(env_body)
      @parse_trees[env_name] = parse_tree
      ## for debug
      # self.show_parse_trees_all
      ##
      begin
        __qv_check(parse_tree)
        __form_check(parse_tree, nametable)
      end
      normalform_env = parse_tree.normalform
      @normalform_envs[env_name] = normalform_env
    }
  end # def parse

  def show_all
    @normalform_envs.each { |env_name, env_body|
      p env_name
      env_body.show
    }
  end

  # for debug
  def show_parse_trees_all
    def __show_parse_trees_all_inter(tree, depth)
      print " " * depth + "e|-"
      p [tree.node.name, tree.node.target]
      tree.succ.each { |succ_i|
        __show_parse_trees_all_inter(succ_i, depth + 1)
      }
    end
    @parse_trees.each { |tree_name, tree_body|
      p tree_name
      __show_parse_trees_all_inter(tree_body, 0)
    }
  end
end
