import YM.Next.RANK.Coordinates
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.Next.RANK.Coordinates for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Station
open MeasureTheory Lattice Wilson RG Filter Set Extraction Cells
open scoped Topology BigOperators

section
variable {c f q : Side} (a : Ratio c f) (b : Ratio f q) (r : Ratio c q)

end

section
variable (A : Schedule) {m k N : ℕ} (p : ℕ) (hm : m≤k) (hN : k≤N)

end

section
variable {G : Gauge} {F : Family G} {k N n : ℕ} {b : ℝ}
variable {x : Points n} (h : FitSky F.path.levels b k x)

include h in
private lemma lifted_costSky (p : ℕ) (i : Fin n) (a : Axis) :
    let A := F.path.levels
    8*((Station.choose A b k x i) a).natAbs ≤ (A.S.toDepth (beforeSky A b k) p).count.val := by
  intro A
  let z := Station.choose A b k x i a
  let T := A.S.toDepth (beforeSky A b k) p
  have he := h.deep i a
  change |A.S.a k * (z:ℝ)| ≤ A.S.a _ / _ at he
  rw [abs_mul, abs_of_pos (A.S.a_pos k),← A.S.embeds_scale T] at he
  have hh : (A.S.a k)*(8*|(z:ℝ)|) ≤ (A.S.a k)* T.count.val := by linarith only [he]
  have hi := le_of_mul_le_mul_left hh (A.S.a_pos k)
  rw [← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] at hi; exact_mod_cast hi

-- location of stamp marker copy on the N-cutoff

def stampSiteSky (F : Family G) (b : ℝ) (x : Points n) (hN : k≤N) (p : ℕ)
    (z : Site (F.side (widthSky F.path.levels b k) p) × Fin n) : Site (F.side N p) :=
  let A := F.path.levels
  let m_le_N := ((widerSky A b k).trans (beforeSky A b k)).trans hN
  (center F.S p m_le_N 0).copyMap z.1 (location F.S k N p (choose A b k x z.2))

lemma exact_campSky (F : Family G) (b : ℝ) (x : Points n) (p) (hN : k≤N)
    (z : Site (F.side (widthSky F.path.levels b k) p) × Fin n) :
    stampSiteSky F b x hN p z=(F.S.toDepth hN p).embed ( (center F.S p ((widerSky F.path.levels b k).trans (beforeSky _ _ _)) 0).copyMap z.1
      (wrap _ (choose F.path.levels b k x z.2))) := from_above F.S p ((widerSky F.path.levels b k).trans (beforeSky ..)) hN ..

include h
lemma at_stopSky (p i) :
    ancestor F.S p (middleSky F.path.levels b k) (beforeSky F.path.levels b k) (wrap _ (choose F.path.levels b k x i)) = 0 := by
  let a := F.path.levels
  let T := F.S.toDepth (beforeSky a b k) p
  let z := choose a b k x i
  let q := T.count.val
  have hp : 0 < q := T.count.property
  apply owner
  rw [show T.embed 0=0 from T.root.map_zero]
  unfold separation; rw [sub_zero]
  have hx : pdist (wrap (F.side k p) z) ≤ q/8 := by
    apply Finset.sup_le; intro j _
    refine (Corona.lap ..).trans ?_
    have ht : 8*(z j).natAbs ≤ q := lifted_costSky h p i j
    omega
  change 2*pdist (wrap (F.side k p) z)<q; omega

lemma FitSky.stop (p : ℕ) (hN : k≤N) (z : Site (F.side (widthSky F.path.levels b k) p) × Fin n) :
    ancestor F.S p (middleSky F.path.levels b k) ((beforeSky F.path.levels b k).trans hN) (stampSiteSky F b x hN p z)=
      (F.S.toDepth (widerSky F.path.levels b k) p).embed z.1 := by
  let a := F.path.levels; let l := middleSky a b k; let m := widthSky a b k
  let s := a.S.toDepth (beforeSky a b k) p
  let t := a.S.toDepth (widerSky a b k) p
  unfold ancestor
  rw [exact_campSky F, parent_nested s (F.S.toDepth hN p) _ (a.S.toDepth_odd _ _) (F.S.toDepth_odd _ _),Ratio.embed_parent,Tiling.copyMap,
    translateBy0,embed_comp t s]
  unfold affine
  rw [parent_offset,s.parent_signed (a.S.toDepth_odd (beforeSky a b k) p),show s.parent (wrap _ (choose a b k x z.2))=0 from at_stopSky h p z.2]
  rw [Signed.act_zero,zero_add]

private lemma spread_costSky (hN : k≤N) (p) (i : Fin n) (j : Axis) :
    let a := F.path.levels
    let T : Ratio (F.S.side (widthSky a b k) p) (F.S.side N p) := F.S.toDepth (((widerSky a b k).trans (beforeSky a b k)).trans hN) p
    let r := F.S.toDepth hN p
    8*((r.count.val • (choose a b k x i) : Cover) j).natAbs ≤ T.count.val := by
  intro a T r; let s := F.S.toDepth (beforeSky a b k) p
  let D := F.S.toDepth (widerSky a b k) p
  let y := F.S.toDepth ((widerSky a b k).trans (beforeSky a b k)) p
  have he : T.count.val=r.count.val*(s.count.val*D.count.val) := by rw [size_comp y r T,size_comp D s y]
  let z := (choose a b k x i j).natAbs
  simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast,he]
  change 8*(r.count.val*z) ≤ _; rw [mul_left_comm]
  exact Nat.mul_le_mul_left _ ((lifted_costSky h p i j).trans (Nat.le_mul_of_pos_right _ D.count.property))

/-- Keep actual positions inside with fixed relative room -- also under copies.
Integer margin rounding includes `1` in the link seam pad. -/
lemma FitSky.margin (p) (hN : k≤N) i :
    let a := F.path.levels
    let T := Cells.center F.S (m:=widthSky a b k) p (((widerSky a b k).trans (beforeSky a b k)).trans hN) 0
    location F.S k N p (choose a b k x i) ∈ T.margin 0 (T.side.val/8) := by
  intro a T
  let r := F.S.toDepth hN p
  let w : Cover := r.count.val • (choose a b k x i)
  let q := T.side.val
  rw [location,dif_pos hN, Ratio.embed_wrap]
  have he (j : Axis) :
      q/8 ≤ T.coordinated 0 (wrap _ w) j ∧ T.coordinated 0 (wrap _ w) j+q/8+1≤q := by
    have hp : 0<q := T.side.property
    have hz : 8*(w j).natAbs ≤ q := spread_costSky h hN p i j
    let z : ℤ := w j + (↑(q/2 : ℕ) : ℤ)
    have ht : 0 ≤ z := by unfold z;omega
    obtain ⟨p₀,hp'⟩ := F.S.toDepth_odd (((widerSky a b k).trans (beforeSky a b k)).trans hN) p; change q = _ at hp'
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
private lemma interiorsSky (d : ℕ) : ∀ᶠ N : ℕ in atTop, ∃ hN : k≤N, ∀ p : ℕ, ∀ z ∈ (F.localSection d).stencil,
    ∀ j : Axis,
      let A := F.path.levels
      let T := center F.S p (((widerSky A b k).trans (beforeSky A b k)).trans hN) 0
      (z j).natAbs<T.side.val/8 := by
  let l := widthSky F.path.levels b k
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

lemma FitSky.stencils (hp : F.Makes) (d : ℕ) : ∀ᶠ N : ℕ in atTop, ∃ hN : k≤N,
    ∀ (p : ℕ) (i : Fin n) (v : F.label d),
      let a := F.path.levels
      let T := Cells.center F.S (m:=widthSky a b k) p (((widerSky a b k).trans (beforeSky a b k)).trans hN) 0
      Interior (T.chamber 0) (F.O N p v (location F.S k N p (choose a b k x i))) := by
  filter_upwards [interiorsSky (F:=F) (k:=k) (b:=b) d] with N H
  obtain ⟨hn,hv⟩ := H
  refine ⟨hn,fun p i v => ?_⟩
  intro a T
  exact Extraction.Around.figure hp T ⟨_,v⟩ _ _ (h.margin p hn i) (hv p)
end
end YM.Next.Rank.Station
