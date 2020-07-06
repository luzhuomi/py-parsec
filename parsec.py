import types

###### Base Monad and @do syntax#########

class Monad:
	def bind(self, func):
		raise NotImplementedError

	def __rshift__(self, bindee):
		return self.bind(bindee)

	def __add__(self, bindee_without_arg):
		return self.bind(lambda _ : bindee_without_arg())

def make_decorator(func, *dec_args):
	def decorator(undecorated):
		def decorated(*args, **kargs):
			return func(undecorated, args, kargs, *dec_args) 
		
		decorated.__name__ = undecorated.__name__
		return decorated
    
	decorator.__name__ = func.__name__
	return decorator

def make_decorator_with_args(func):
	def decorator_with_args(*dec_args):
		return make_decorator(func, *dec_args)
	return decorator_with_args

decorator           = make_decorator
decorator_with_args = make_decorator_with_args

@decorator_with_args
def do(func, func_args, func_kargs, Monad):
    @handle_monadic_throws(Monad)
    def run_maybe_iterator():
        itr = func(*func_args, **func_kargs)

        if isinstance(itr, types.GeneratorType):
            @handle_monadic_throws(Monad)
            def send(val):
                try:
                    # here's the real magic
                    monad = itr.send(val) 
                    return monad.bind(send)
                except StopIteration:
                    return Monad.unit(None)
                
            return send(None)
        else:
            #not really a generator
            if itr is None:
                return Monad.unit(None)
            else:
                return itr
    # print func.__name__
    return run_maybe_iterator()

@decorator_with_args
def handle_monadic_throws(func, func_args, func_kargs, Monad):
    try:
        return func(*func_args, **func_kargs)
    except MonadReturn, ret:
        return Monad.unit(ret.value)
    except Done, done:
        assert isinstance(done.monad, Monad)
        return done.monad

class MonadReturn(Exception):
    def __init__(self, value):
        self.value = value
        Exception.__init__(self, value)

class Done(Exception):
    def __init__(self, monad):
        self.monad = monad
        Exception.__init__(self, monad)

def mreturn(val):
    raise MonadReturn(val)

def done(val):
    raise Done(val)

def fid(val):
    return val


########### Parsec Monad ###########
class Parsec(Monad):
	def __init__(self, run):
		self.run = run
	# >>=
	def bind(self, bindee):
		run0 = self.run
		
		def run1(tokens):
			v = run0(tokens)
			if v is not None:
				(result,rest) = v
				return bindee(result).run(rest)
			else:
				return v
		return Parsec(run1)
	# return?
	@classmethod
	def unit(cls, val):
		return cls(lambda tokens: (val, tokens))

def mzero(): # fail parser
	def run(tokens): 
		return None
	return Parsec(run)

def item():
	''' unconditionally parse a single item
	'''
	def run(tokens):
		if len(tokens) == 0:
			return None
		else:
			return (tokens[0],tokens[1:])
	return Parsec(run)


def sat(condition):
	''' match if it satisfies the condition
	'''
	def m(): # we wrap around a function to delay the generation of the monad, this is needed because of the repeat combinator
		def run(tokens):
			mb_r = item().run(tokens)
			if mb_r:
				(c,cs) = mb_r
				if condition(c):
					return mb_r
				else: 
					return None
			else:
				return None
		return Parsec(run)
	return m



# same as below		
def sat2(condition):
	@do(Parsec)
	def m():
		val = yield item()
		if condition(val):
			mreturn(val)
		else:
			yield mzero()
			# mzero()
			# can't use return here, because we are in the do sequence
			# can't invoke mzero() either, because we do not want ot execute the zero monad 
			# while we generating the sequence, the type will be wrong.
	return m
		
	
# deterministic first choice
# todo: implementing it in do syntax?
def choice(p1,p2):
	def m():
		def run(tokens):
			r1 = p1().run(tokens)
			if r1:
				return r1
			else:
				return p2().run(tokens)
		return Parsec(run)
	return m

# return empty list
def empty_list():
	def run(tokens):
		return ([],tokens)
	return Parsec(run)



# repetitions
''' does not work, with some funny type error
@do(Parsec)
def many(p):
	yield choice(many1(p), empty_list())

@do(Parsec)
def many1(p):
	x = yield p
	xs = yield many(p)
	mreturn([x]+xs)
'''


def repeat(p):
	@do(Parsec)
	def m():
		'''
		repeating, we can't take p directly, because p will be a non-repeatable iterator, 
		instead of take a generator of p.
		'''
		ls = []
		while True:
			i = yield choice(p, empty_list)()
			if i <> []:
				ls.append(i)
			else:
				mreturn(ls)
		mreturn(ls)
	return m

def option(p):
	@do(Parsec)
	def m():
		i = yield choice(p, empty_list)()
		if i <> []:
			mreturn(i)
		else:
			mreturn(None)
	return m

def sequence(p1,p2):
	@do(Parsec)
	def m():
		i = yield p1()
		j = yield p2()
		mreturn((i,j))
	return m

'''
def sequence2(p1,p2):
	def run(tokens):
		r1 = p1().run(tokens)
		if r1:
			(x1,tokens1) = r1
			r2 = p2().run(tokens1)
			if r2:
				(x2,tokens2) = r2
				return ((x1,x2), tokens2)
			else:
				return None
		else:
			return None
	return Parsec(run)
'''

# interleaving

def interleave(parse_one,parse_delim):
	@do(Parsec)
	def m():
		fst = yield parse_one()
		ls = [fst]
		while True:
			r = yield choice(sequence(parse_delim,parse_one), empty_list)()
			if r <> []:
				(d,i) = r
				ls.append(i)
			else:
				mreturn(ls)
		mreturn(ls)
	return m

# get everything until condition is satisfied by the current token, which will be comsumed.
def everythinguntil(condition):
	@do(Parsec)
	def m():
		ls = []
		while True:
			i = yield item()
			if condition(i):
				mreturn(ls)
			else:
				ls.append(i)
		mreturn(ls)
	return m

# ########## parsing json #
v='{"x":1,"b":[1,2,3]}'

@do(Parsec)
def parse_json():
	''' parse a json 
	'''
	json = yield choice(parse_jint,
			    choice(parse_jstr,
				   choice(parse_jmap,parse_jlist)))()
	mreturn(json)
					  


@do(Parsec)
def parse_jint():
	''' parse an int
	'''
	i,is_ = yield sequence(parse_digit,repeat(parse_digit))()
	v = i
	for x in is_:
		v = v*10 + x
	mreturn(v)


@do(Parsec)
def parse_digit():
	''' parse one digit
	'''
	i = yield sat(lambda x:x.isdigit())()
	mreturn(int(i))

@do(Parsec)
def parse_jstr():
	''' parse a string
	'''
	lq = yield sat(lambda x:x=='"')()
	ts = yield everythinguntil(lambda x:x=='"')()
	s = ''.join(ts)
	mreturn(s)


@do(Parsec)
def parse_jlist():
	''' parse [ ... ]
	'''
	lb = yield sat(lambda x:x=='[')()
	jsons = yield interleave(parse_json, sat(lambda x:x==','))()
	rb = yield sat(lambda x:x==']')()
	
	jlist = []
	for json in jsons:
		jlist.append(json)
	mreturn(jlist)

@do(Parsec)
def parse_jmap():
	''' parse {name:value, ...}
	'''
	lb = yield sat(lambda x:x=='{')()
	nvps = yield interleave(parse_nvp, sat(lambda x:x==','))()
	rb = yield sat(lambda x:x=='}')()

	jmap = {}
	for nvp in nvps:
		name,v = nvp
		jmap[name]=v
	mreturn(jmap)
	
	
@do(Parsec)
def parse_nvp():
	''' parse a name:value pair
	'''
	name = yield parse_name()
	col  = yield sat(lambda x:x==':')()
	v    = yield parse_json()
	mreturn((name,v))

@do(Parsec)
def parse_name():
	''' parse a name
	'''
	lq = yield sat(lambda x:x=='"')()
	ts = yield everythinguntil(lambda x:x=='"')()
	s = ''.join(ts)
	mreturn(s)

	

# testing

@do(Parsec)
def trial1():
	val1 = yield sat(lambda x:x=='a')()  # first monad op in the iterator
	val2 = yield sat(lambda x:x=='a')() # second monad op in the iterator
	val3 = yield sat(lambda x:x=='a')() # third monad op in the iterator
	# print (val1,val2,val3)
	mreturn(val1+val2+val3)  # get out of the iteration 

@do(Parsec)
def trial2():
	val1 = yield choice(sat2(lambda x:x=='a'),sat2(lambda x:x=='b'))()  # first monad op in the iterator
	val2 = yield sat(lambda x:x=='a')() # second monad op in the iterator
	val3 = yield sat(lambda x:x=='a')() # third monad op in the iterator
	# print (val1,val2,val3)
	mreturn(val1+val2+val3)  # get out of the iteration 


@do(Parsec)
def trial3():
	# val1 = yield many1(sat2(lambda x:x=='a'))
	# val1 = yield choice(many1(sat(lambda x:x=='a')),empty_list()) 
	val1 = yield repeat(sat(lambda x:x=='a'))()
	val2 = yield repeat(sat(lambda x:x=='b'))()
	mreturn(val1+val2)


@do(Parsec)
def trial4():
	val1 = yield interleave(sat(lambda x:x=='a'),sat(lambda x:x=='b'))()
	mreturn(val1)

@do(Parsec)
def trial5():
	val1 = yield everythinguntil(lambda x:x=='a')()
	mreturn(val1)

@do(Parsec)
def trial6():
	val1 = yield interleave(sequence(sat(lambda x:x=='a'), sat(lambda x:x=='a')), sat(lambda x:x=='b'))()
	mreturn(val1)

@do(Parsec)
def trial7():
	val1 = yield repeat(choice(sequence(sat(lambda x:x==','), sequence(sat(lambda x:x=='a'),sat(lambda x:x=='a'))), empty_list))()
	mreturn(val1)

	

def parsec_example():
	print trial1().run("aa") 


		
