#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <refinedc.h>

//@rc::import pgtable_free from refinedc.project.page_table_walker.pgtable_free

typedef uint32_t u32;
typedef uint64_t u64;
typedef u64 phys_addr_t;

typedef u64 kvm_pte_t;

#define BITS_PER_LONG 64

[[rc::parameters("i : Z")]]
[[rc::args("i @ int<i32>")]]
[[rc::requires("{0 ≤ i < 64}")]]
[[rc::returns("{bf_mask_cons i 1 bf_nil} @ bitfield_raw<u64>")]]
[[rc::tactics("all: have ? := Z_shiftl_1_range i 64; try solve_goal.")]]·
[[rc::lemmas("bf_mask_bit")]]
u64 BIT(int i)
{
    return (1UL << (i));
}

[[rc::parameters("h : Z", "l : Z")]]
[[rc::args("h @ int<i32>", "l @ int<i32>")]]
[[rc::requires("{0 ≤ l}", "{l < h < 64}")]]
[[rc::returns("{bf_mask_cons l (h - l + 1) bf_nil} @ bitfield_raw<u64>")]]
[[rc::tactics("all: have [??] : 1 ≤ 1 ≪ l ≤ 2^64 - 1 by apply Z_shiftl_1_range; solve_goal.")]]
[[rc::tactics("all: try have -> : max_int u64 = 2^64 - 1 by solve_goal.")]]
[[rc::tactics("all: try have -> : ly_size i64 * 8 = bits_per_int u64 by solve_goal.")]]
[[rc::tactics("all: try have -> : bits_per_int u64 = 64 by solve_goal.")]]
[[rc::tactics("all: try have -> : Z_lunot 64 0 = 2^64 - 1 by solve_goal.")]]
[[rc::tactics("all: try solve_goal.")]]
[[rc::lemmas("bf_mask_gen")]]
u64 GENMASK(int h, int l)
{
    return (((~0UL) - (1UL << (l)) + 1) & (~0UL >> (BITS_PER_LONG - 1 - (h))));
}

#define __bf_shf(x) (__builtin_ffsll(x) - 1)

[[rc::parameters("r : Z", "a : Z", "k : Z", "res : Z")]]
[[rc::args("{bf_mask_cons a k bf_nil} @ bitfield_raw<u64>", "r @ bitfield_raw<u64>")]]
[[rc::requires("{0 ≤ a}", "{0 < k}", "{a + k ≤ 64}")]]
[[rc::requires("{normalize_bitfield_eq (bf_slice a k r) res}")]]
[[rc::returns("res @ int<u64>")]]
[[rc::tactics("all: unfold normalize_bitfield_eq in *; subst.")]]
[[rc::tactics("all: try rewrite Z.add_simpl_r Z_least_significant_one_nonempty_mask.")]]
[[rc::tactics("all: try solve_goal.")]]
[[rc::lemmas("bf_mask_cons_singleton_nonempty", "bf_shr_singleton")]]
u64 FIELD_GET(u64 _mask, u64 _reg)
{
    return (((_reg) & (_mask)) >> __bf_shf(_mask));
}

#define WRITE_ONCE(x, val) (x) = (val)

#define __AC(X, Y) (X##Y)
#define _AC(X, Y) __AC(X, Y)
#define _UL(x) (_AC(x, UL))
#define UL(x) (_UL(x))
// #define BIT(nr) (UL(1) << (nr))
#define GENMASK(h, l) (((~UL(0)) - (UL(1) << (l)) + 1) & (~UL(0) >> (BITS_PER_LONG - 1 - (h))))

// #define FIELD_GET(_mask, _reg) (typeof(_mask))(((_reg) & (_mask)) >> __bf_shf(_mask))
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

typedef struct
[[rc::refined_by("l : Z", "pte : {option Pte}", "ts : {list (tree Pte)}")]]
[[rc::constraints("{0 <= l}", "{l < 4}", "{length ts = 512%nat}")]]
[[rc::ptr_type("pgtable_ptr_t: ∃ p. p @ &own<...> & {pte_loc_agree l pte p}")]]
pgtable {
  [[rc::field("guarded<array<u64, {(pgtree_to_next_pgtable_refinement l <$> ts) `at_type` !{optionalO<λ rfmt. rfmt @ pgtable_ptr_t, null_pte @ bitfield<Pte>>}}>>")]]
  u64 val[PTRS_PER_PTE];
}* pgtable_ptr_dummy;

struct kvm_pgtable_walk_data {
  struct kvm_pgtable *pgt;
  u64 addr;
  u64 end;
};

[[rc::refined_by("ia : Z", "l : Z", "ts : {list (tree Pte)}")]]
struct kvm_pgtable {
  [[rc::field("ia @ int<u32>")]]
  u32 ia_bits;
  [[rc::field("l @ int<u32>")]]
  u32 start_level;
  [[rc::field("{l, None, ts} @ pgtable_ptr_t")]]
  kvm_pte_t *pgd;
};

void mm_ops_put_page(void *addr);
void mm_ops_free_pages_exact(void *addr, unsigned long size);

void *mm_ops_phys_to_virt(phys_addr_t phys);

[[rc::parameters("l : Z")]]
[[rc::args("l @ int<u32>")]]
[[rc::requires("{l < 4}")]]
[[rc::returns("{granule_shift l} @ int<u64>")]]
[[rc::lemmas("granule_shift_def")]]
static u64 kvm_granule_shift(u32 level) {
  return ARM64_HW_PGTABLE_LEVEL_SHIFT(level);
}

[[rc::parameters("l : Z")]]
[[rc::args("l @ int<u32>")]]
[[rc::requires("{0 ≤ l}", "{l < 4}")]]
[[rc::returns("{bf_mask_cons (granule_shift l) 1 bf_nil} @ bitfield_raw<u64>")]]
[[rc::tactics("all: rewrite <-granule_shift_def; solve_goal.")]]
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

// dangerous specification: effectively int-to-ptr
static u64 kvm_pte_to_phys(kvm_pte_t pte) {
  u64 pa = pte & KVM_PTE_ADDR_MASK;

  return pa;
}

// just an offset but why and how to specify it?
static kvm_pte_t *kvm_pte_follow(kvm_pte_t pte) {
  return mm_ops_phys_to_virt(kvm_pte_to_phys(pte));
}

[[rc::parameters("pte : Pte")]]
[[rc::args("pte @ bitfield<Pte>")]]
[[rc::requires("{bitfield_wf pte}")]]
[[rc::returns("{pte_valid pte} @ builtin_boolean")]]
static bool kvm_pte_valid(kvm_pte_t pte) { return 0 != (pte & KVM_PTE_VALID); }

[[rc::parameters("pte : Pte", "level : Z")]]
[[rc::args("pte @ bitfield<Pte>", "level @ int<u32>")]]
[[rc::requires("{bitfield_wf pte}")]]
[[rc::returns("{bool_decide (pte_discriminate level pte = Table)} @ builtin_boolean")]]
[[rc::lemmas("pte_discriminate_3_not_table")]]
[[rc::tactics("\
    case pte0; unfold pte_discriminate; case (level =? 3) eqn: Hl; try done.\
    rewrite Z.eqb_eq in Hl.\
    contradiction.\
")]]
static bool kvm_pte_table(kvm_pte_t pte, u32 level) {
  if (level == KVM_PGTABLE_MAX_LEVELS - 1)
    return false;

  if (!kvm_pte_valid(pte))
    return false;

  return FIELD_GET(KVM_PTE_TYPE, pte) == KVM_PTE_TYPE_TABLE;
}

[[rc::parameters("l: loc", "pte : Pte")]]
[[rc::args("l @ &own<pte @ bitfield<Pte>>")]]
[[rc::requires("{bitfield_wf pte}")]]
[[rc::ensures("own l : null_pte @ bitfield<Pte>")]]
static void kvm_clear_pte(kvm_pte_t *ptep)
{
	WRITE_ONCE(*ptep, 0);
}

[[rc::parameters("p : Z")]]
[[rc::args("p @ int<u64>")]]
[[rc::returns("{bool_decide (p ≠ 0)} @ builtin_boolean")]]
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
