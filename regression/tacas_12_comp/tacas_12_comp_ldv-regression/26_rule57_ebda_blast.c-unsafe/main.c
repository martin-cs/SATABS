# 1 "files/rule57_ebda_blast.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "files/rule57_ebda_blast.c"
# 1 "./assert.h" 1

void __blast_assert()
{
 ERROR: goto ERROR;
}
# 2 "files/rule57_ebda_blast.c" 2









struct hotplug_slot;

struct bus_info {
};

struct slot {
 int a;
 int b;
 struct hotplug_slot * hotplug_slot;
 struct bus_info *bus_on;
};

struct hotplug_slot {
 struct slot *private;
 int b;
};






struct slot *tmp_slot;
int used_tmp_slot = 0;
int freed_tmp_slot = 1;

extern void * kzalloc(int, int);

void kfree(void *p) {
 if(p!=0 && p==tmp_slot)
  freed_tmp_slot = 1;
}

extern struct bus_info *ibmphp_find_same_bus_num();

extern int fillslotinfo(struct hotplug_slot *);
extern int ibmphp_init_devno(struct slot **);

int ebda_rsrc_controller() {
 struct hotplug_slot *hp_slot_ptr;

 struct bus_info *bus_info_ptr1;
 int rc;

 hp_slot_ptr = kzalloc(sizeof(*hp_slot_ptr), 1);
 if(!hp_slot_ptr) {
  rc = -2;
  goto error_no_hp_slot;
 }
 hp_slot_ptr->b = 5;

 tmp_slot = kzalloc(sizeof(*tmp_slot), 1);

 if(!tmp_slot) {
  rc = -2;
  goto error_no_slot;
 }

 used_tmp_slot = 0;
 freed_tmp_slot = 0;

 tmp_slot->a = 2;
 tmp_slot->b = 3;

 bus_info_ptr1 = ibmphp_find_same_bus_num();
 if(!bus_info_ptr1) {
  rc = -3;





  goto error;
 }
 tmp_slot->bus_on = bus_info_ptr1;
 bus_info_ptr1 = 0;

 tmp_slot->hotplug_slot = hp_slot_ptr;

 hp_slot_ptr->private = tmp_slot;
 used_tmp_slot = 1;

 rc = fillslotinfo(hp_slot_ptr);
 if(rc)
  goto error;

 rc = ibmphp_init_devno((struct slot **) &hp_slot_ptr->private);
 if(rc)
  goto error;

 return 0;

error:
 kfree(hp_slot_ptr->private);
error_no_slot:

error_no_hp_slot:

 return rc;
}

void main() {
 ebda_rsrc_controller();
 if(!used_tmp_slot)
  ((freed_tmp_slot) ? (0) : __blast_assert ());
}
