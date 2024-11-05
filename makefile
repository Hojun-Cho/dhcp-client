
all: dhcp

dhcp:
	cc *.c -o $@

clean:
	rm -f dhcp


