import YM.TraceExtension.LogScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Finite-order polylogarithmic expansion tools. Signed integer powers of s,
*nonnegative* integer powers of log. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Wick
open Set Filter Function Asymptotics
open scoped Topology BigOperators Classical

abbrev past := 𝓝[>] (0:ℝ)
lemma mostly : ∀ᶠ s in past, 0<s ∧ s<1 := by
    filter_upwards [self_mem_nhdsWithin,(gt_mem_nhds (show 0<(1:ℝ) from zero_lt_one)).filter_mono nhdsWithin_le_nhds] with k hk hv using ⟨hk,hv⟩

/-- Ensure global multiplication rule -/
def fill (x : ℝ) := if 0<x then x else 1
lemma fill_away (x : ℝ) : fill x≠ 0 := by unfold fill; split; positivity; norm_num
lemma fill_at {x : ℝ} (h : 0<x) : fill x=x := if_pos h

def tile (a : ℤ) := fun x=> fill x ^ a
def joint (a : ℤ) (k : ℕ) := fun x=> tile a x * Real.log (fill x)^k
def board := Submodule.span ℝ {f:ℝ→ℝ | ∃ a k, f= joint a k}
lemma jointBoard (a k) : joint a k ∈ board := Submodule.subset_span (show ∃ _ _, _ from ⟨a,k,rfl⟩)
lemma tileBoard (a) : tile a ∈ board := by
    convert jointBoard a 0 using 1; ext1 x; simp [joint]
lemma one_board : (1:ℝ→ℝ)∈ board := by convert tileBoard 0 using 1; ext x; simp [tile]
lemma joinTiles (a b : ℤ) : tile (a+b)= tile a*tile b := funext fun x=> zpow_add₀ (fill_away x) a b
lemma board_mul (f g : ℝ→ℝ) (h : f∈board) (k : g∈board) : f*g∈board := by
    unfold board at h k
    induction h using Submodule.span_induction with
    | mem t ht =>
        rcases ht with ⟨a,v,rfl⟩
        induction k using Submodule.span_induction with
        | mem r hr=>
          rcases hr with ⟨b,w,rfl⟩
          rw [show joint a v*joint b w=joint (a+b) (v+w) by ext; simp only [joint, joinTiles,pow_add,Pi.mul_apply]; ring]; exact jointBoard _ _
        | zero=> rw [mul_zero]; exact board.zero_mem
        | add x y _ _ hx hy=> rw [mul_add]; exact board.add_mem hx hy
        | smul t x _ hx=> rw [mul_smul_comm]; exact board.smul_mem _ hx
    | zero=> rw [zero_mul]; exact board.zero_mem
    | add x y _ _ hx hy=> rw [add_mul]; exact board.add_mem hx hy
    | smul t x _ hx=> rw [smul_mul_assoc]; exact board.smul_mem _ hx

/-- expansion at order integer k possibly diverging -/
def AtOrder (f : ℝ→ℝ) (k : ℤ) := ∃ g∈board,(f-g) =O[past] tile k
def Expands (f : ℝ→ℝ) := ∀ i : ℤ, AtOrder f i

lemma tile_cost {a b : ℤ} (h : a≤b) : tile b =O[past] tile a := by
    apply isBigO_iff.mpr; refine ⟨1,?_⟩; filter_upwards [mostly] with x hx
    unfold tile; rw [fill_at hx.1,one_mul,Real.norm_of_nonneg (zpow_nonneg hx.1.le b),Real.norm_of_nonneg (zpow_nonneg hx.1.le a)]; exact zpow_le_zpow_right_of_le_one₀ hx.1 hx.2.le h
lemma cost_mul {a b : ℤ} {f g : ℝ→ℝ} (h : f=O[past] tile a) (k : g=O[past] tile b) : (f*g)=O[past] tile (a+b) := by rw [joinTiles]; exact h.mul k
lemma allows {f : ℝ→ℝ} {a b : ℤ} (h : a≤b) : AtOrder f b → AtOrder f a := by rintro ⟨x,y,hx⟩; exact ⟨x,y,hx.trans (tile_cost h)⟩
lemma board_bound (f) (h : f∈board) : ∃ i : ℤ, f=O[past] tile i := by
    unfold board at h
    induction h using Submodule.span_induction with
    | mem t ht=>
      obtain ⟨a,v,rfl⟩:=ht
      refine ⟨a+ -(v:ℤ), cost_mul (tile_cost (le_refl a)) ?_⟩
      apply isBigO_iff.mpr; refine ⟨1,?_⟩; filter_upwards [mostly] with x hx
      unfold tile; rw [fill_at hx.1, Real.norm_eq_abs,← pow_abs
      ]; have he : |Real.log x| ≤ x⁻¹ := by
        rw [abs_of_nonpos (Real.log_nonpos hx.1.le hx.2.le),← Real.log_inv]; exact Real.log_le_self (inv_pos.mpr hx.1).le
      calc _ ≤ (x⁻¹)^v := pow_le_pow_left₀ (abs_nonneg _) he _
           _ = _ := by rw [one_mul,Real.norm_of_nonneg (zpow_nonneg hx.1.le _),zpow_neg, zpow_natCast, inv_pow]
    | zero=> exact ⟨0,isBigO_of_le _ fun x=> (by change ‖(0:ℝ)‖ ≤ _; simp)⟩
    | add x y _ _ H K=>
        obtain ⟨a,ha⟩:=H; obtain ⟨b,hb⟩:=K; exact ⟨min a b,(ha.trans (tile_cost (min_le_left ..))).add (hb.trans (tile_cost (min_le_right ..)))⟩
    | smul t x _ h=> obtain ⟨a,h⟩:=h; exact ⟨a,h.const_mul_left t⟩

lemma cost_order {f : ℝ→ℝ} {k : ℤ} (h : f=O[past] tile k) : AtOrder f k := ⟨0,board.zero_mem,by rwa [sub_zero]⟩
lemma own {f : ℝ→ℝ} (h : f∈board) : Expands f := fun i=> ⟨f,h,isBigO_of_le _ fun _=> by simp⟩
lemma AtOrder.plus {f g} {k} (h : AtOrder f k) (p : AtOrder g k) : AtOrder (f+g) k := by
    obtain ⟨x,y,hx⟩:=h; obtain ⟨z,w,hz⟩:=p
    exact ⟨x+z,board.add_mem y w, (show f+g-(x+z)=f-x+(g-z) by abel).symm ▸ hx.add hz⟩
lemma AtOrder.scale {f k} (h : AtOrder f k) (t : ℝ) : AtOrder (t • f) k := by
    obtain ⟨x,p,hx⟩:=h; exact ⟨t • x,board.smul_mem t p, by rw [← smul_sub]; exact hx.const_mul_left t⟩
lemma AtOrder.shift {f k} (h : AtOrder f k) (a : ℤ) : AtOrder (tile a*f) (a+k) := by
    obtain ⟨x,p,hx⟩:=h; exact ⟨tile a*x,board_mul _ _ (tileBoard a) p,by rw [← mul_sub]; exact cost_mul (tile_cost le_rfl) hx⟩
lemma AtOrder.upon {f g k} (h : AtOrder f k) (p : f=ᶠ[past] g) : AtOrder g k := by
    obtain ⟨x,y,h⟩:=h; exact ⟨x,y,h.congr' (p.sub (Filter.EventuallyEq.refl _ _)) EventuallyEq.rfl⟩
lemma Expands.plus {f g : ℝ→ℝ} (h : Expands f) (p : Expands g) : Expands (f+g) := fun _=> AtOrder.plus (h _) (p _)
lemma Expands.scale {f : ℝ→ℝ} (h : Expands f) (t : ℝ) : Expands (t • f) := fun _=> AtOrder.scale (h _) t
lemma Expands.bound {f : ℝ→ℝ} (h : Expands f) : ∃ i:ℤ, f=O[past] tile i := by
    obtain ⟨x,y,h⟩:= h 0; obtain ⟨k,hk⟩ := board_bound x y
    refine ⟨min k 0,?_⟩; have he : (f-x+x)=O[past] tile (min k 0) := (h.trans (tile_cost (min_le_right ..))).add (hk.trans (tile_cost (min_le_left ..)))
    rwa [sub_add_cancel] at he
lemma Expands.mult {f g} (h : Expands f) (p : Expands g) : Expands (f*g) := by
    intro i
    obtain ⟨l,hl⟩ := p.bound; obtain ⟨x,hx,hM⟩ := h (i-l)
    obtain ⟨u,U⟩ := board_bound x hx; obtain ⟨y,hy,hN⟩:= p (i-u)
    have hp : f*g-x*y=(f-x)*g+x*(g-y) := by ring
    refine ⟨x*y,board_mul _ _ hx hy,by
      rw [hp]; exact (show ((f-x)*g)=O[past] tile i by simpa only [sub_add_cancel] using cost_mul hM hl).add (show (x*(g-y))=O[past] tile i by simpa only [add_sub_cancel] using cost_mul U hN)⟩
end YM.TraceExtension.Wick
