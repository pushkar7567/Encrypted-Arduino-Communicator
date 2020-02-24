//------------------------------------------------------
// Names: Amro Amanuddein and Pushkar Sabharwal
// ID's: 1572498 (Amro) 1588927 (Pushkar) 
// CMPUT274, Fall 2019
// 
// Assignment 2 Part 2: Encrypted Arduino Communication
//------------------------------------------------------
#include <Arduino.h>
// Declaring global constant variables to be used later for encryption and decryption 
const int Pin13 = 13;
const int analogPin = 1;
// Setup function for the Arduinos
void setup(){
	init();
	Serial.begin(9600);
	Serial3.begin(9600);
	pinMode(Pin13, INPUT);
	pinMode(analogPin,INPUT);
	
}
// This function determines which arduino is server and which is client
bool Client_or_Server() {
	bool isServer;
	if (digitalRead(Pin13) == HIGH){
		isServer = true;
	}
	else{
		isServer = false;

	}
	return isServer;
}
//Declration of states of server and client for handshaking protocol
enum States {
	Start, Listen, WaitForAck, WaitingForKey, DataExchange, WaitingForKey2
};
// Checks if numer n is prime or not, implemented from primality morning problem
bool is_Prime(uint32_t n) {
	int prime_check=0;
	for(int i=2;(i*i)<=n;){
		if (n%i==0) {
			prime_check++;
			i++;		
		}
		if (n%i!=0){
			i++;
		}
	}
	if (prime_check==0) {
		return true;
	}
	if (prime_check!=0){
		return false;
	}
}
// Function generates a random number
uint32_t random_num(uint32_t n) {
	uint32_t generated=0;
	for (int i=0; i<(n-1); i++) {
		int number= analogRead(analogPin);
		int least_bit = number&1;
// Update the random number 
		generated = generated + least_bit*pow(2,i);
		Serial.flush();
// Delay for 10 ms to allow the voltage to fluctuate
		delay(10);
	}
	generated=generated ^ (uint32_t) 1<< (n-1);
	return generated;
}
// Separate function to generate a prime number that is in the range [2^k-1,2^k)
uint32_t generate_prime(int n) {
	bool is_prime= 0;
	uint32_t prime_num=0;
	while (is_prime==0) {
		prime_num= random_num(n);
// Use of the prime checker function		
		is_prime= is_Prime(prime_num);
	}
	return prime_num;

}
// Mulmod function used in powmod to prevent overflow, by computed a*b (mod m)
uint32_t mulmod(uint32_t a, uint32_t b, uint32_t m){
	uint32_t result = 0;
	uint32_t next_bit = 1;
	for (int i=0; i < 31; i++){
		if (i == 0 ){
			next_bit = b%m;
		
		} else {
			next_bit = (2%m)*(next_bit%m) % m;
		}
		if (a&1) {
			result += (next_bit % m) % m;
		}
		a = a >> 1;
		result = result % m;
	}
	return result;
}	
// Greatest common divisor function implemented in class
uint32_t gcd(uint32_t a,uint32_t b){
	while(b>0){
		a%=b;
		uint32_t temporary= a;
		a=b;
		b=temporary;
	}
	return a;
}


// Powmod function that was created in class computes x^e (mod n)
uint32_t powmod(uint32_t x, uint32_t e, uint32_t n){
	uint32_t ans = 1;
	uint32_t pow_x = x;
	while (e != 0){
		if (e&1){
			ans = mulmod(ans,pow_x,n);

		}
	pow_x = mulmod(pow_x,pow_x,n);
	e >>= 1;
	}
	return ans;
}
// This given function writes a uint32_t to Serial 3, it starts from LS byte to MS byte  
void uint32_to_serial3(uint32_t num){
	Serial3.write((char) (num >> 0 ));
	Serial3.write((char) (num >> 8 ));
	Serial3.write((char) (num >> 16 ));
	Serial3.write((char) (num >> 24 ));
}
// This given function reads uint32_t from Serial 3, starting from LS byte to MS byte.
uint32_t uint32_from_serial3(){
	uint32_t num = 0;
	num = num | ((uint32_t) Serial3.read()) << 0;
	num = num | ((uint32_t) Serial3.read()) << 8;
	num = num | ((uint32_t) Serial3.read()) << 16;
	num = num | ((uint32_t) Serial3.read()) << 24;
	return num;
}

// Given function waits for a certain number of bytes on Serial3 or for timeout
bool wait_on_serial3( uint8_t nbytes, long timeout){
	unsigned long deadline = millis() + timeout;
	while (Serial3.available()<nbytes && (timeout < 0 || millis() < deadline))
	{
		delay(1); 
	}
	return Serial3.available() >= nbytes;
}
// Generates our public key, e such that 1<e<phi(n) and gcd(e,phi(n))=1
uint32_t generate_e(uint32_t phi_n){
	uint32_t generated = generate_prime(15);
	while(gcd(generated,phi_n)!=(uint32_t)1){
		generated+=(uint32_t)1;
	}
	return generated;
}
// This calculates our private key, d such that e*d is equavilant to 1 (congruent). 
uint32_t modular_inverse(uint32_t e, uint32_t phi_n) {
	uint32_t d;
	uint32_t i=1;
	long q;
	long r[40];
	int32_t s[40];
	int32_t t[40];
	r[0] = e;
	r[1] = phi_n;
	s[0]= 1;
	s[1]=0;
	t[0]=0;
	t[1]=1;
// The process follows that of the worksheet on eClass
	while (r[i]>0) {
		q = r[i-1]/r[i];          
		r[i+1] = (r[i-1] - q*r[i]);  
		s[i+1] = (s[i-1] - q*s[i]);
		t[i+1] = (t[i-1] - q*t[i]);
		i +=1;
	}

	if(s[i-1] < 0) {
		while(s[i-1]<0){
			s[i-1]+=phi_n;
		}
		return d = s[i-1];
	}else if(phi_n < s[i-1]) {
		d = s[i-1]%phi_n;
		return d;
	}else if ((s[i-1] > 0) && (s[i-1]<phi_n)) {
		d = s[i-1];
		return d;
	}
}
int main(){
	setup();
	bool isServer = Client_or_Server();
	uint32_t d,n,m,phi_n,e,p,q;
// If statement to determine who is server and who is client 
	if (isServer==true){
// Server side key generation
		p = generate_prime(15);
		q = generate_prime(16);
		n = p*q;
		phi_n = (p-1)*(q-1);
		e = generate_e(phi_n);
		d = modular_inverse(e,phi_n);
		//Declaring the initial state of the finite state code for server
		States state = Listen;
		while (state != DataExchange){
			if (state == Listen){
				//Reading the Acknowledgement
				if (wait_on_serial3(1,1000)){
					char ACKc = Serial3.read();
					if (ACKc=='C'){
						Serial.println("C received");
						state = WaitingForKey;
					}
				}
				//Timeout if takes higher than 1 second to get acknowledgement
				else {
					Serial.println("Timeout");
				}
				
			}else if (state == WaitingForKey){
				//Receving and sending public key and mod from and to client and sending acknowledgement
				if (wait_on_serial3(8,1000)){
					uint32_t ckey = uint32_from_serial3();
					uint32_t cmod = uint32_from_serial3();
					Serial.println("Keys received");
					Serial.println("Sending ACK with keys");
					Serial3.write('A');
					uint32_to_serial3(e);
					uint32_to_serial3(n);
					e = ckey;
					m = cmod;
					state = WaitForAck;
				}else{
					Serial.println("Timeout");
					state = Listen;
				}
			//This state is only attained if 'A' acknowlegement is not received	
			}else if (state == WaitingForKey2){
				if (wait_on_serial3(8,1000)){
					uint32_t ckey = uint32_from_serial3();
					uint32_t cmod = uint32_from_serial3();
					Serial.println("Keys received");
					Serial.println("Sending ACK with keys");
					uint32_to_serial3(e);
					uint32_to_serial3(n);
					e = ckey;
					m = cmod;
					state = WaitForAck;
				}else{
					Serial.println("Timeout");
					state = Listen;
				}
			//This state is attined after waiting for key, goes to DataExchange if 'A' received	
			}else if (state == WaitForAck){
				if (wait_on_serial3(1,1000)){
					char samp = Serial3.read();
					if (samp == 'A'){
						Serial.println("Received ACK");
						state = DataExchange;
					}
					else if (samp == 'C'){
						state = WaitingForKey2;
					}
				}

				else {
					Serial.println("Timeout");
					state = Listen;
				}

			}

		}
	}
	else {
// Client side key generation
			p = generate_prime(15);
			q = generate_prime(16);
			n = p*q;
			phi_n = (p-1)*(q-1);
			e = generate_e(phi_n);
			d = modular_inverse(e,phi_n);
			States state = Start;
			while (state != DataExchange){
			if (state == Start){
				Serial.println("Sending CR");
				Serial3.write('C');
				uint32_to_serial3(e);
				uint32_to_serial3(n);
				state = WaitForAck;
			}

			else if (state == WaitForAck){
				if (wait_on_serial3(1,1000)){
					if (Serial3.read()== 'A'){
						if(wait_on_serial3(8,1000)){
						uint32_t skey = uint32_from_serial3();
						uint32_t smod = uint32_from_serial3();
						e = skey;
						m = smod;
						Serial.println("Keys received");
						Serial.println("Sending ACK");
						Serial3.write('A');
						state = DataExchange;
						}			
						else {
							Serial.println("Timeout");
							state = Start; 
						}	
					}
				}
			else{
				Serial.println("Timeout");
				state=Start;
			}	
		}

		}
	}	

	Serial.println("Connection Established! You may chat now! ");
	while(true){
		if (Serial.available() > 0){
				uint32_t x = Serial.read();
// If the enter key is pressed, using the ASCII value, we go newline.
				if (x == 13){
					Serial.write(char(x));
					uint32_t encrypted = powmod(x,e,m);
					uint32_to_serial3(encrypted);
					uint32_t newline = 10;
					uint32_t newline_encrypt = powmod(newline,e,m);
					uint32_to_serial3(newline_encrypt);
					Serial.write(char(newline));
				}
				else{
// Typed letters/numbers will appear on "typer's" screen
					Serial.write(char(x));
// Letters/numbers/words get encrypted and sent 
					uint32_t encrypted = powmod(x,e,m);
					uint32_to_serial3(encrypted);

				}
		}		

// Must process 3 bits first		
		else if (Serial3.available() > 3){
				uint32_t y = uint32_from_serial3();
				uint32_t decrypted = powmod(y,d,n);
// If the decrypted ASCII value is that of ENTER (/r), we go to newline
				if (decrypted == 13){
					uint32_t decrypt_nl= uint32_from_serial3();
					uint32_t nl = powmod(decrypt_nl,d,n);
					Serial.write(char(nl));
				}
				Serial.write(char(decrypted));
			
		} 
	}
	Serial.flush();	
}
	