struct slice {
  int length;
  uint8_t *buffer; // uint8_t * == Buffer.buffer
  // buffer.length == length
};

struct validation {
  bool result;
  int bytes_read; // no need for bytes_read if result == false
} // option U32.t

validation validate_u16_array(slice b) {
  if (b.length < 2) {
    return {false, 0};
  }
  uint16_t length = read_u16_be(b.buffer[:2]);
  if (b.length + 2 < length) {
    return {false, 0};
  }
  return {true, 2 + length};
}
