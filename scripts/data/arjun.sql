DROP TABLE IF EXISTS data;
CREATE TABLE data (
  solver STRING NOT NULL,
  dirname STRING NOT NULL,
  fname STRING NOT NULL,

  timeout_t FLOAT NOT NULL,
  timeout_mem FLOAT NOT NULL,
  timeout_call TEXT NOT NULL,
  page_faults INT NOT NULL,
  signal INT NOT NULL,

  arjun_sha1 TEXT NOT NULL,
  sbva_sha1 TEXT NOT NULL,
  cms_sha1 TEXT NOT NULL,

  input_vars INT,
  start_to_define_vars INT,
  orig_total_vars INT,

  puura_time FLOAT,
  puura_defined INT,

  extend_time FLOAT,
  extend_defined INT,

  backward_time FLOAT,
  backward_defined INT,

  manthan_sampling_time FLOAT,
  manthan_training_time FLOAT,
  manthan_repair_time FLOAT,
  manthan_time FLOAT,
  repairs INT,
  repairs_failed INT,
  manthan_defined INT,

  arjun_time FLOAT
);
.mode csv
.import --skip 1 mydata.csv data
UPDATE data SET timeout_t = NULL WHERE timeout_t = '';
UPDATE data SET timeout_mem = NULL WHERE timeout_mem = '';
UPDATE data SET timeout_call = NULL WHERE timeout_call = '';
UPDATE data SET page_faults = NULL WHERE page_faults = '';
UPDATE data SET signal = NULL WHERE signal = '';
UPDATE data SET input_vars = NULL WHERE input_vars = '';
UPDATE data SET start_to_define_vars = NULL WHERE start_to_define_vars = '';
UPDATE data SET orig_total_vars = NULL WHERE orig_total_vars = '';
UPDATE data SET puura_time = NULL WHERE puura_time = '';
UPDATE data SET puura_defined = NULL WHERE puura_defined = '';
UPDATE data SET extend_time = NULL WHERE extend_time = '';
UPDATE data SET extend_defined = NULL WHERE extend_defined = '';
UPDATE data SET backward_time = NULL WHERE backward_time = '';
UPDATE data SET backward_defined = NULL WHERE backward_defined = '';
UPDATE data SET manthan_sampling_time = NULL WHERE manthan_sampling_time = '';
UPDATE data SET manthan_training_time = NULL WHERE manthan_training_time = '';
UPDATE data SET manthan_repair_time = NULL WHERE manthan_repair_time = '';
UPDATE data SET manthan_time = NULL WHERE manthan_time = '';
UPDATE data SET repairs = NULL WHERE repairs = '';
UPDATE data SET repairs_failed = NULL WHERE repairs_failed = '';
UPDATE data SET manthan_defined = NULL WHERE manthan_defined = '';
UPDATE data SET arjun_time = NULL WHERE arjun_time = '';
