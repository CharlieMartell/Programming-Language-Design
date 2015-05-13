PROJ = omgrofl
TEST = test.omgrofl
KOMPILE-FLAGS = ""
KRUN-FLAGS = --output none 
all: run

run: .changed
		krun $(KRUN-FLAGS) ${TEST}

test:
		ktest tests/config.xml

.changed: $(PROJ).k
		kompile $(KOMPILE-FLAGS) $(PROJ).k
			touch .changed

clean:
		rm -rf $(PROJ)-kompiled
			rm -f .changed
