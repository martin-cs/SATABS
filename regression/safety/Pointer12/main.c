typedef unsigned char    uint8_t;
typedef unsigned short   uint16_t;
typedef unsigned int     uint32_t;

#ifndef TOSH_DATA_LENGTH
#define TOSH_DATA_LENGTH 28
#endif

typedef struct message_t {
  uint8_t header[2];   // sizeof(message_header_t)];
  uint8_t data[TOSH_DATA_LENGTH];
  uint8_t footer[2];   // sizeof(message_footer_t)];
  uint8_t metadata[2]; // sizeof(message_metadata_t)];
} message_t;

//Data structure for storing sensor data
typedef struct sensor_data {
  uint32_t seq_no;
  uint16_t hum;
  uint16_t temp;
  uint16_t tsr;
  uint16_t par;
} sensor_data_t;

message_t send_msg;
sensor_data_t* sensor_data; 

void* radioGetPayload(message_t* msg, uint8_t len);

/*
  gives a surprising VERIFICATION SUCCESSFUL when run for all claims, 
  and the expected FAILED for --claim 3
*/

int main() {
  sensor_data =
    (sensor_data_t*)radioGetPayload(&send_msg, sizeof(sensor_data_t));

  if(sensor_data)
    sensor_data->seq_no = 0;    // claims 1,2

  assert(0);                    // claim 3
}

uint8_t radioMaxPayloadLength()
{
  return TOSH_DATA_LENGTH;
}

void* radioGetPayload(message_t* msg, uint8_t len)
{
  if (len > radioMaxPayloadLength()) 
    return 0;

  else 
    return (void*)msg->data;
}
