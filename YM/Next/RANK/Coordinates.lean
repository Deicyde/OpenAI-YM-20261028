import YM.Corona.Spend
import YM.Extraction.Held
import YM.Next.RANK.Tuning


/-!
# Offset compatibility and interior

All copies on the true torus, even near period seams. The comparisons will
start at these cutoff links; show the selected rounded layouts sit well in
their width cells and remain jointly on-grid down to depth k. Also compute
later ancestor at the middle stop. These checks need the *composition* of
actual centered blocks (odd factors). A port pretending a choice of any
nearest point could give incompatible blocking for reflected clusters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Station
open MeasureTheory Lattice Wilson RG Filter Set Extraction Cells
open scoped Topology BigOperators

section
variable {c f q : Side} (a : Ratio c f) (b : Ratio f q) (r : Ratio c q)

lemma size_comp : r.count.val=b.count.val*a.count.val := by
  have he : c.val*r.count.val=c.val*(b.count.val*a.count.val) := by rw [← r.exact_size,b.exact_size,a.exact_size]; ring
  exact (Nat.mul_right_inj c.property.ne').mp he

lemma embed_comp (x : Site c) : r.embed x=b.embed (a.embed x) := by
  rw [Ratio.embed,Ratio.embed, a.lift_embed,smul_smul, size_comp a b]

lemma separation_pos (x y : Site f) (h : x ≠ y) : 1 ≤ separation x y :=
  Nat.pos_of_ne_zero fun H => h ((Corona.line_home x y).symm.trans (Corona.line_end x y H.le))

lemma both (x y : Site c) : separation (a.embed x) (a.embed y) = a.count.val*separation x y := by
  apply le_antisymm _ (Corona.below a ..)
  unfold separation
  rw [← a.root_embed,← a.root_embed,← map_sub,a.root_embed]
  refine Finset.sup_le ?_; intro i _
  rw [a.lift_embed]
  simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (component_le _ _)

lemma midway (h : Odd a.count.val) (x : Site f) : 2*separation x (a.embed (a.parent x)) < a.count.val := by
  obtain ⟨i,hi⟩ := h; have he := Corona.near a x; omega

lemma owner (x : Site f) (y : Site c) (h : 2 * separation x (a.embed y)< a.count.val) : a.parent x=y := by
  by_contra ho
  have hp : a.count.val ≤ separation (a.embed (a.parent x)) (a.embed y) := by
    rw [both]; exact Nat.le_mul_of_pos_right _ (separation_pos _ _ ho)
  have ht := separation_triangle (a.embed (a.parent x)) x (a.embed y)
  rw [separation_comm _ x] at ht; have := Corona.near a x; omega

lemma parent_nested (p : Odd a.count.val) (w : Odd b.count.val) (x : Site q) : r.parent x=a.parent (b.parent x) := by
  let y := b.parent x
  let z := a.parent y
  apply owner
  change 2 * separation x (r.embed z)< r.count.val
  rw [embed_comp a b,size_comp a b]
  have he := Nat.mul_le_mul_left 2 (separation_triangle x (b.embed y) (b.embed (a.embed z)))
  rw [both b] at he
  refine he.trans_lt ?_
  have ht : 2*separation y (a.embed z)+1 ≤ a.count.val := midway a p y
  have hf : 2*separation x (b.embed y) < b.count.val := midway b w x
  linarith only [Nat.mul_le_mul_left b.count.val ht,hf]

lemma parent_offset (x : Site f) (k : Site c) : a.parent (x+a.embed k)=a.parent x+k := by
  have hz : a.assemble (a.parent x+k,a.residue x)=x+a.embed k := by
    rw [Ratio.assemble,(show a.embed (a.parent x+k)=a.embed (a.parent x)+a.embed k from a.root.map_add _ _),
      add_right_comm (a.embed (a.parent x)), a.unpack_at]
  rw [← hz]; exact a.assemble_parent _
end

section
variable (A : Schedule) {m k N : ℕ} (p : ℕ) (hm : m≤k) (hN : k≤N)

lemma translateBy0 (z : Site (A.side m p)) :
    (center A p hm 0).translateBy z=(A.toDepth hm p).embed z := by
  have ht := copy_home A hm (p:=p) 0 z
  simpa only [Tiling.copyMap,affine,Signed.act_zero,zero_add] using ht

lemma on_pattern (z : Site (A.side m p)) (x : Site (A.side k p)) : (center A p (hm.trans hN) 0).copyMap z ((A.toDepth hN p).embed x) =
    (A.toDepth hN p).embed ((center A p hm 0).copyMap z x) := by
  let Y := center A p hm 0; let B := A.toDepth hN p
  let X := center A p (hm.trans hN) 0
  have ho : X.omega z=Y.omega z := rfl
  rw [Tiling.copyMap,Tiling.copyMap,translateBy0,translateBy0, embed_comp (A.toDepth hm p) B (A.toDepth (hm.trans hN) p) z]
  simp only [affine]; change _ = B.root ( (Y.omega z).act x+_)
  rw [map_add, Ratio.root_embed B, B.signed]; simp only [Ratio.root_embed]; rfl

lemma from_above (x : Cover) (z : Site (A.side m p)) : (center A p (hm.trans hN) 0).copyMap z (location A k N p x) =
    (A.toDepth hN p).embed ((center A p hm 0).copyMap z (wrap _ x)) := by rw [location,dif_pos hN, on_pattern]

/-- Anchor includes all marker names at duplicated positions; operation uses
*one* point per slot, independent of markers selected in estimates. -/
def ancestor (i : ℕ) (hi : i ≤ N) (z : Site (A.side N p)) := (A.toDepth hi p).parent z

end

section
variable {G : Gauge} {F : Family G} {k N n : ℕ} {b : ℝ}
variable {x : Points n} (h : Fit F.path.levels b k x)

include h in
private lemma lifted_cost (p : ℕ) (i : Fin n) (a : Axis) :
    let A := F.path.levels
    8*((Station.choose A b k x i) a).natAbs ≤ (A.S.toDepth (before A b k) p).count.val := by
  intro A
  let z := Station.choose A b k x i a
  let T := A.S.toDepth (before A b k) p
  have he := h.deep i a
  change |A.S.a k * (z:ℝ)| ≤ A.S.a _ / _ at he
  rw [abs_mul, abs_of_pos (A.S.a_pos k),← A.S.embeds_scale T] at he
  have hh : (A.S.a k)*(8*|(z:ℝ)|) ≤ (A.S.a k)* T.count.val := by linarith only [he]
  have hi := le_of_mul_le_mul_left hh (A.S.a_pos k)
  rw [← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] at hi; exact_mod_cast hi

-- location of stamp marker copy on the N-cutoff

def stampSite (F : Family G) (b : ℝ) (x : Points n) (hN : k≤N) (p : ℕ)
    (z : Site (F.side (width F.path.levels b k) p) × Fin n) : Site (F.side N p) :=
  let A := F.path.levels
  let m_le_N := ((wider A b k).trans (before A b k)).trans hN
  (center F.S p m_le_N 0).copyMap z.1 (location F.S k N p (choose A b k x z.2))

lemma exact_camp (F : Family G) (b : ℝ) (x : Points n) (p) (hN : k≤N)
    (z : Site (F.side (width F.path.levels b k) p) × Fin n) :
    stampSite F b x hN p z=(F.S.toDepth hN p).embed ( (center F.S p ((wider F.path.levels b k).trans (before _ _ _)) 0).copyMap z.1
      (wrap _ (choose F.path.levels b k x z.2))) := from_above F.S p ((wider F.path.levels b k).trans (before ..)) hN ..



include h
lemma at_stop (p i) :
    ancestor F.S p (middle F.path.levels b k) (before F.path.levels b k) (wrap _ (choose F.path.levels b k x i)) = 0 := by
  let a := F.path.levels
  let T := F.S.toDepth (before a b k) p
  let z := choose a b k x i
  let q := T.count.val
  have hp : 0 < q := T.count.property
  apply owner
  rw [show T.embed 0=0 from T.root.map_zero]
  unfold separation; rw [sub_zero]
  have hx : pdist (wrap (F.side k p) z) ≤ q/8 := by
    apply Finset.sup_le; intro j _
    refine (Corona.lap ..).trans ?_
    have ht : 8*(z j).natAbs ≤ q := lifted_cost h p i j
    omega
  change 2*pdist (wrap (F.side k p) z)<q; omega

lemma Fit.stop (p : ℕ) (hN : k≤N) (z : Site (F.side (width F.path.levels b k) p) × Fin n) :
    ancestor F.S p (middle F.path.levels b k) ((before F.path.levels b k).trans hN) (stampSite F b x hN p z)=
      (F.S.toDepth (wider F.path.levels b k) p).embed z.1 := by
  let a := F.path.levels; let l := middle a b k; let m := width a b k
  let s := a.S.toDepth (before a b k) p
  let t := a.S.toDepth (wider a b k) p
  unfold ancestor
  rw [exact_camp F, parent_nested s (F.S.toDepth hN p) _ (a.S.toDepth_odd _ _) (F.S.toDepth_odd _ _),Ratio.embed_parent,Tiling.copyMap,
    translateBy0,embed_comp t s]
  unfold affine
  rw [parent_offset,s.parent_signed (a.S.toDepth_odd (before a b k) p),show s.parent (wrap _ (choose a b k x z.2))=0 from at_stop h p z.2]
  rw [Signed.act_zero,zero_add]



private lemma spread_cost (hN : k≤N) (p) (i : Fin n) (j : Axis) :
    let a := F.path.levels
    let T : Ratio (F.S.side (width a b k) p) (F.S.side N p) := F.S.toDepth (((wider a b k).trans (before a b k)).trans hN) p
    let r := F.S.toDepth hN p
    8*((r.count.val • (choose a b k x i) : Cover) j).natAbs ≤ T.count.val := by
  intro a T r; let s := F.S.toDepth (before a b k) p
  let D := F.S.toDepth (wider a b k) p
  let y := F.S.toDepth ((wider a b k).trans (before a b k)) p
  have he : T.count.val=r.count.val*(s.count.val*D.count.val) := by rw [size_comp y r T,size_comp D s y]
  let z := (choose a b k x i j).natAbs
  simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast,he]
  change 8*(r.count.val*z) ≤ _; rw [mul_left_comm]
  exact Nat.mul_le_mul_left _ ((lifted_cost h p i j).trans (Nat.le_mul_of_pos_right _ D.count.property))

/-- Keep actual positions inside with fixed relative room -- also under copies.
Integer margin rounding includes `1` in the link seam pad. -/
lemma Fit.margin (p) (hN : k≤N) i :
    let a := F.path.levels
    let T := Cells.center F.S (m:=width a b k) p (((wider a b k).trans (before a b k)).trans hN) 0
    location F.S k N p (choose a b k x i) ∈ T.margin 0 (T.side.val/8) := by
  intro a T
  let r := F.S.toDepth hN p
  let w : Cover := r.count.val • (choose a b k x i)
  let q := T.side.val
  rw [location,dif_pos hN, Ratio.embed_wrap]
  have he (j : Axis) :
      q/8 ≤ T.coordinated 0 (wrap _ w) j ∧ T.coordinated 0 (wrap _ w) j+q/8+1≤q := by
    have hp : 0<q := T.side.property
    have hz : 8*(w j).natAbs ≤ q := spread_cost h hN p i j
    let z : ℤ := w j + (↑(q/2 : ℕ) : ℤ)
    have ht : 0 ≤ z := by unfold z;omega
    obtain ⟨p₀,hp'⟩ := F.S.toDepth_odd (((wider a b k).trans (before a b k)).trans hN) p; change q = _ at hp'
    have hs : q/8 ≤ z.toNat ∧ z.toNat+q/8+1≤q := by unfold z; omega
    have hv : T.coordinated 0 (wrap _ w) j=z.toNat := by
      unfold Tiling.coordinated; rw [T.starts_zero]
      let B := F.side N p
      have h₀ : wrap B w j - T.base j = ((z.toNat:ℕ) : Per B) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg ht]
        change (w j : Per B) - (0-((q/2:ℕ):Per B)) = ((w j + (↑(q/2 : ℕ) : ℤ):ℤ): Per B)
        simp only [Int.cast_add,Int.cast_natCast]; ring
      have hm : q<B.val := T.narrow
      rw [h₀, ZMod.val_natCast_of_lt (by omega : z.toNat < B.val)]
    rw [hv]; exact hs
  refine ⟨fun j => ?_,fun j => he j⟩
  change T.coordinated 0 (wrap _ w) j < q; have hh := (he j).2; omega



omit h in
private lemma interiors (d : ℕ) : ∀ᶠ N : ℕ in atTop, ∃ hN : k≤N, ∀ p : ℕ, ∀ z ∈ (F.localSection d).stencil,
    ∀ j : Axis,
      let A := F.path.levels
      let T := center F.S p (((wider A b k).trans (before A b k)).trans hN) 0
      (z j).natAbs<T.side.val/8 := by
  let l := width F.path.levels b k
  have he (z : Cover) (i : Axis) : ∀ᶠ N in atTop, F.S.a N * (↑(8*((z i).natAbs+1)):ℝ) ≤ F.S.a l := by
    have hv := F.S.shrinks.mul_const ((8*((z i).natAbs+1):ℕ) : ℝ); rw [zero_mul] at hv
    exact hv.eventually (ge_mem_nhds (F.S.a_pos l))
  have hs := eventually_all_finset _|>.2 (fun z (_:z∈(F.localSection d).stencil) => eventually_all.mpr (he z))
  filter_upwards [eventually_ge_atTop k,hs] with N hN h
  refine ⟨hN,fun p z hz i => ?_⟩
  intro A T
  have hh := h z hz i
  have ht : F.S.a N * ((8*((z i).natAbs+1):ℕ):ℝ) ≤ F.S.a N*T.side.val := hh.trans_eq (F.S.embeds_scale T.units).symm
  have hv : 8*((z i).natAbs+1) ≤ T.side.val := by exact_mod_cast (le_of_mul_le_mul_left ht (F.S.a_pos N))
  omega

lemma Fit.stencils (hp : F.Makes) (d : ℕ) : ∀ᶠ N : ℕ in atTop, ∃ hN : k≤N,
    ∀ (p : ℕ) (i : Fin n) (v : F.label d),
      let a := F.path.levels
      let T := Cells.center F.S (m:=width a b k) p (((wider a b k).trans (before a b k)).trans hN) 0
      Interior (T.chamber 0) (F.O N p v (location F.S k N p (choose a b k x i))) := by
  filter_upwards [interiors (F:=F) (k:=k) (b:=b) d] with N H
  obtain ⟨hn,hv⟩ := H
  refine ⟨hn,fun p i v => ?_⟩
  intro a T
  exact Extraction.Around.figure hp T ⟨_,v⟩ _ _ (h.margin p hn i) (hv p)
end
end YM.Next.Rank.Station
