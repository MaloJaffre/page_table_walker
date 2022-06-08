#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef uint32_t u32;
typedef uint64_t u64;
typedef u64 size_t;
typedef u64 phys_addr_t;
typedef u64 kvm_pte_t; // page descriptor bitfield -> in Coq could be: just list
                       // flags * option phys_addr

#define BITS_PER_LONG 64
#define __AC(X, Y) (X##Y)
#define _AC(X, Y) __AC(X, Y)
#define _UL(x) (_AC(x, UL))
#define UL(x) (_UL(x))
#define BIT(nr) (UL(1) << (nr))
#define GENMASK(h, l) (((~UL(0)) - (UL(1) << (l)) + 1) & (~UL(0) >> (BITS_PER_LONG - 1 - (h))))
#define __bf_shf(x) (__builtin_ffsll(x) - 1)
#define FIELD_GET(_mask, _reg) (typeof(_mask))(((_reg) & (_mask)) >> __bf_shf(_mask))
#define ALIGN_DOWN(x, a) __ALIGN_KERNEL((x) - ((a)-1), (a))
#define __ALIGN_KERNEL(x, a) __ALIGN_KERNEL_MASK(x, (typeof(x))(a)-1)
#define __ALIGN_KERNEL_MASK(x, mask) (((x) + (mask)) & ~(mask))

#define PAGE_SHIFT 12
#define PAGE_SIZE (_AC(1, UL) << PAGE_SHIFT)
#define PAGE_MASK (~((1 << PAGE_SHIFT) - 1))
#define PTRS_PER_PTE (1 << (PAGE_SHIFT - 3))
#define ARM64_HW_PGTABLE_LEVEL_SHIFT(n) ((PAGE_SHIFT - 3) * (4 - (n)) + 3)

#define KVM_PGTABLE_MAX_LEVELS 4U
#define KVM_PTE_VALID BIT(0)
#define KVM_PTE_TYPE BIT(1)
#define KVM_PTE_TYPE_TABLE 1
#define KVM_PTE_ADDR_MASK GENMASK(47, PAGE_SHIFT)
#define KVM_PTE_ADDR_51_48 GENMASK(15, 12)


// page table is ftree pte where: depth = 4, node width = 512
struct kvm_pgtable_walk_data {
  struct kvm_pgtable *pgt;
  u64 addr;
  u64 end;
};

struct kvm_pgtable {
  u32 ia_bits;
  u32 start_level;
  kvm_pte_t *pgd;
};

void mm_ops_put_page(void *addr);
void mm_ops_free_pages_exact(void *addr, unsigned long size);
void *mm_ops_phys_to_virt(
    phys_addr_t phys); // 	return (void *)((phys_addr_t)(phys) -
                       // hyp_physvirt_offset);

static u64 kvm_granule_shift(u32 level) {
  /* Assumes KVM_PGTABLE_MAX_LEVELS is 4 */
  return ARM64_HW_PGTABLE_LEVEL_SHIFT(level);
}

static u64 kvm_granule_size(u32 level) { return BIT(kvm_granule_shift(level)); }

static u32 kvm_pgtable_idx(struct kvm_pgtable_walk_data *data, u32 level) {
  u64 shift = kvm_granule_shift(level);
  u64 mask = BIT(PAGE_SHIFT - 3) - 1;

  return (data->addr >> shift) & mask;
}

static u32 __kvm_pgd_page_idx(struct kvm_pgtable *pgt, u64 addr) {
  u64 shift = kvm_granule_shift(pgt->start_level - 1); /* May underflow */
  u64 mask = BIT(pgt->ia_bits) - 1;

  return (addr & mask) >> shift;
}

static u32 kvm_pgd_page_idx(struct kvm_pgtable_walk_data *data) {
  return __kvm_pgd_page_idx(data->pgt, data->addr);
}

static u32 kvm_pgd_pages(u32 ia_bits, u32 start_level) {
  struct kvm_pgtable pgt = {
      .ia_bits = ia_bits,
      .start_level = start_level,
  };

  return __kvm_pgd_page_idx(&pgt, -1ULL) + 1;
}

static u64 kvm_pte_to_phys(kvm_pte_t pte) {
  u64 pa = pte & KVM_PTE_ADDR_MASK;

  if (PAGE_SHIFT == 16)
    pa |= FIELD_GET(KVM_PTE_ADDR_51_48, pte) << 48;

  return pa;
}

static kvm_pte_t *kvm_pte_follow(kvm_pte_t pte) {
  return mm_ops_phys_to_virt(kvm_pte_to_phys(pte));
}

static bool kvm_pte_valid(kvm_pte_t pte) { return pte & KVM_PTE_VALID; }

static bool kvm_pte_table(kvm_pte_t pte, u32 level) {
  if (level == KVM_PGTABLE_MAX_LEVELS - 1)
    return false;

  if (!kvm_pte_valid(pte)) // simple function
    return false;

  return FIELD_GET(KVM_PTE_TYPE, pte) == KVM_PTE_TYPE_TABLE;
}

static bool stage2_pte_is_counted(kvm_pte_t pte) { return !!pte; }

static int stage2_free_walker(u32 level, kvm_pte_t *ptep) {
  kvm_pte_t pte = *ptep;

  if (!stage2_pte_is_counted(pte))
    return 0;

  mm_ops_put_page(ptep);

  if (kvm_pte_table(pte, level))
    mm_ops_put_page(kvm_pte_follow(pte));

  return 0;
}

int destroy_inner_walk(struct kvm_pgtable_walk_data *data, kvm_pte_t *pgtable,
                       u32 level);

int destroy_inner_visit(struct kvm_pgtable_walk_data *data, kvm_pte_t *ptep,
                        u32 level) {
  int ret = 0;
  u64 addr = data->addr;
  kvm_pte_t *childp, pte = *ptep;
  bool table = kvm_pte_table(pte, level);

  // flag not set for destroy walker
  // if (table && (flags & KVM_PGTABLE_WALK_TABLE_PRE)) {
  //   ret = stage2_free_walker(level, ptep, data->walker->args);
  // }

  if (!table) {
    ret = stage2_free_walker(level, ptep);
    pte = *ptep;
    table = kvm_pte_table(pte, level);
  }

  if (ret)
    goto out;

  if (!table) {
    data->addr = ALIGN_DOWN(data->addr, kvm_granule_size(level));
    data->addr += kvm_granule_size(level); // simple match function
    goto out;
  }

  childp = kvm_pte_follow(pte);
  ret = destroy_inner_walk(data, childp, level + 1l);
  if (ret)
    goto out;

  ret = stage2_free_walker(level, ptep);

out:
  return ret;
}

int destroy_inner_walk(struct kvm_pgtable_walk_data *data, kvm_pte_t *pgtable,
                       u32 level) {
  u32 idx;
  int ret = 0;

  // if (WARN_ON_ONCE(level >= KVM_PGTABLE_MAX_LEVELS)) {
  // 	ret = -EINVAL;
  // 	goto out;
  // }

  for (idx = kvm_pgtable_idx(data, level); idx < PTRS_PER_PTE; ++idx) {
    kvm_pte_t *ptep = &pgtable[idx];

    if (data->addr >= data->end)
      break;

    ret = destroy_inner_visit(data, ptep, level);
    if (ret)
      break;
  }

out:
  return ret;
}

void kvm_pgtable_stage2_destroy(struct kvm_pgtable *pgt) {
  size_t pgd_sz;

  struct kvm_pgtable_walk_data walk_data = {
      .pgt = pgt,
      .addr = 0,
      .end = BIT(pgt->ia_bits),
  };

  // u64 limit = BIT(pgt->ia_bits);

  // if (data->addr > limit || data->end > limit)
  // 	return -ERANGE;

  // if (!pgt->pgd)
  // 	return -EINVAL;
  u32 idx;
  for (idx = kvm_pgd_page_idx(&walk_data); walk_data.addr < walk_data.end;
       ++idx) {
    kvm_pte_t *ptep = &pgt->pgd[idx * PTRS_PER_PTE];

    if (destroy_inner_walk(&walk_data, ptep, pgt->start_level))
      break;
  }

  pgd_sz = kvm_pgd_pages(pgt->ia_bits, pgt->start_level) * PAGE_SIZE;
  mm_ops_free_pages_exact(pgt->pgd, pgd_sz);
  pgt->pgd = NULL;
}

// need to specify
