require "qprocess.rb"

class ProcessParser
  def initialize()
    @parsed_processes = Hash.new #H["proc_name"] = QProcess
  end
  attr_accessor :parsed_processes

  private
  def __tokenize(node) # for '.' construction
    tmp_node = QProcess::ProcessNode.new
    if i = node.index("!") #send
      unless i != 0 and node[i+1]
        raise "ill formed send constructor: " + node
      end
      tmp_node.kind = "send"
      tmp_node.name = node[0..i-1]
      tmp_node.target = [node[i+1..node.length-1]]
    elsif i = node.index("?") #receive
      unless node[i-1] and node[i+1]
        raise "ill formed receive constructor: " + node
      end
      tmp_node.kind = "receive"
      tmp_node.name = node[0..i-1]
      tmp_node.target = [node[i+1..node.length-1]]
    else
      unless (i = node.index("[")) and (j = node.index("]"))
        raise "ill formed constructor: " + node
      end
      tmp_node.kind = "oper"
      tmp_node.name = node[0 .. i-1]
      tmp_node.target = node[i+1 .. j-1].split(",")
    end
    tmp_node
  end #__tokenize
  
  # only parses according to the syntax.
  # declaration and binding of qvars are
  # checked by __form_check.
  def __parse_inter(process)
    parsed_process = QProcess.new
    tmp_node = QProcess::ProcessNode.new
    proclen = process.length

    if process[0..5] == "*meas*"
      head = 6
      tail = 0
      nest_if = 0
      cond_set_flag = false;
      then_set_flag = false;

      i = 0;
      process.each_char { |char|
        if process[i..i+5] == "*meas*"
          nest_if += 1
        elsif process[i..i+5] == "*saem*" and nest_if >= 2
          nest_if -= 1
        elsif process[i..i+3] == "then" and nest_if == 1
          cond_set_flag = true;
          tail = i - 1
          tmp_node.kind = "condition"
          tmp_node.target = [process[head..tail]]
          head = i + 4
          parsed_process.node = tmp_node
        elsif process[i..i+5] == "*saem*" and nest_if == 1
          then_set_flag = true;
          tail = i - 1
          parsed_process.left = __parse_inter(process[head..tail])
        end
        i += 1
      }
      unless cond_set_flag and then_set_flag
        raise "measure syntax error"
      end
    elsif process[0..0] == "(" #either palla or ristriction
      i = 0
      nest_paren = 0
      process.each_char{ |char|
        if char == "("
          nest_paren += 1
        elsif char == ")"
          nest_paren -= 1
        elsif char == "|" and nest_paren == 1 #palla
          unless process[i+1..i+1] == "|" and 
                 process[proclen-1..proclen-1] == ")"
            raise "palla syntax error"
          end
          tmp_node.kind = "palla"
          parsed_process.node = tmp_node
          parsed_process.left = __parse_inter(process[1..i-1])
          parsed_process.right = __parse_inter(process[i+2..proclen-2])
          break
        elsif char == "/" and nest_paren == 1 #ristriction
          unless process[i+1..i+1] == "{" and 
              process[proclen-1..proclen-1] == ")" and
              process[proclen-2..proclen-2] == "}" 
            raise "restriction syntax error"
          end
          tmp_node.kind = "restriction"
          tmp_node.target = process[i+2 .. proclen-3].split(",")
          parsed_process.node = tmp_node
          parsed_process.left = __parse_inter(process[1..i-1])
          break
        end
        i += 1
      } #process.each_char
    else
      i = 0
      terminal_flag = true
      process.each_char{ |char|
        if char == "."
          parsed_process.node = __tokenize(process[0..i-1])
          parsed_process.left = __parse_inter(process[i+1..proclen - 1])
          terminal_flag = false
          break
        end
        i += 1
      }
      if terminal_flag == true
        begin 
          i = process.index("(")
          j = process.index(")")
          if i == nil or j == nil or process[0..6] != "discard"
            raise "ill formed discard: " + process
          end
          tmp_node.kind = "discard"
          tmp_node.target = process[i+1 .. j-1].split(",")
          parsed_process.node = tmp_node
        end
      end
    end
    parsed_process
  end #__parse_inter

  # __form_check checks 
  # declaration and binding of each qvar
  # declaration and type of each operator
  def __form_check(process_name, 
                   parsed_process,
                   bound_qvars,
                   nametable) #recursive
    new_bound = Hash.new;

    case parsed_process.node.kind
    when "nil"
      # do nothing
    when "send"
      channel = parsed_process.node.name
      qvars    = parsed_process.node.target
      unless (ch_len = nametable.channels[channel])
        raise "undeclared channel: " + channel
      end
      unless (qv_len = bound_qvars[qvars[0]]) or (qv_len = nametable.qvars[qvars[0]])
        raise "unbound qvar: #{qvars[0]}"
      end
      unless ch_len == qv_len
        raise "lengths (#{ch_len}, #{qv_len}) of channel and qvar are not coincide: #{qvars[0]}, in #{process_name}"
      end
    when "receive"
      channel = parsed_process.node.name
      qvars   = parsed_process.node.target
      unless (ch_len = nametable.channels[channel])
        raise "undeclared channel: #{channel} in #{process_name}, in #{process_name}"
      end
      if RUBY_VERSION >= '1.9'
        if bound_qvars.key(qvars[0]) or nametable.qvars[qvars[0]]
          raise "already bounded qvar: #{qvars[0]} in #{process_name}, in #{process_name}"
        end
      else
        if bound_qvars.index(qvars[0]) or nametable.qvars[qvars[0]]
          raise "already bounded qvar: #{qvars[0]} in #{process_name}, in #{process_name}"
        end
      end
      new_bound[qvars[0]] = ch_len
    when "oper"
      operator = parsed_process.node.name
      argument = parsed_process.node.target
      unless nametable.operators[operator]
        raise "undeclared operator: #{operator} in #{process_name}"      
      end
      arg_i = 0
      argument.each{ |qvar|
        unless (qv_len_i = bound_qvars[qvar]) or (qv_len_i = nametable.qvars[qvar])
          raise "unbouded qvar: #{qvar} in #{process_name}"
        end
        unless qv_len_i == (nametable.operators[operator])[arg_i]
          raise "#{qvar}'s length #{qv_len_i} is wrong, expected #{(nametable.operators[operator])[arg_i]} for #{operator}, in #{process_name}"
        end
        arg_i += 1
        qv_len_i = nil
      }
    when "palla"
      #do nothing
    when "condition"
      condition = parsed_process.node.target
      begin
        unless (con_len = bound_qvars[condition[0]]) or
            (con_len = nametable.qvars[condition[0]])
          raise "unbouded qvar: #{condition[0]} in #{process_name}"
        end
        unless con_len == "1"
          raise "condition qvar is not a qubit #{condition[0]}"
        end
      end
    when "restriction"
      restricted_chans = parsed_process.node.target;
      restricted_chans.each{ |channel|
        begin
          unless nametable.channels[channel]
            raise "undeclared channel: #{channel} in #{process_name}"
          end
        end
      }
    end #case
    unless parsed_process.left == nil
      __form_check(process_name,
                   parsed_process.left,
                   bound_qvars.merge(new_bound),
                   nametable)
    end
    unless parsed_process.right == nil
      __form_check(process_name,
                   parsed_process.right,
                   bound_qvars.merge(new_bound),
                   nametable)
    end
  end # __form_check

  public
  def parse_all(processes, nametable)
    processes.each{ |process_name, process_body|
      parsed_process = __parse_inter(process_body)
      bound_qvars = Hash.new
      begin
        __form_check(process_name,
                     parsed_process,
                     bound_qvars,
                     nametable)
      end
      @parsed_processes[process_name] = parsed_process
    }
  end

  def show_all
    @parsed_processes.each { |process_name, process_body|
      p process_name
      process_body.show_tree
    }
  end
end
