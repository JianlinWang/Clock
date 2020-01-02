theory listClock imports Complex_Main begin

datatype clock =Nil | Cons (infixl "|." 60 ) 'real clock

end