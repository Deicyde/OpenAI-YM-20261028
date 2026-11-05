import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Cells.OnGrid
import YM.Cells.Proximity
import YM.Complex.Columns
import YM.Overlay.Table


/-!
# Cell fit at every actual cutoff level beyond the marks

Link seams: odd number of steps. We pay a fixed relative margin of
1/4 in positions and give also the native `Tiling.margin` consequence.
No rotation of empty/no marker assumptions needed. Centers transported
literally, preserves k-sublattice. Periods even, as in `Family.S`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Positions
open MeasureTheory Set Function Lattice Wilson RG Cells Extraction Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators

section AnyGeom
variable (S : Schedule)

private lemma halfFit {r N p} (h : r ≤ N) (z : Cover) (H : ∀ a, |S.gridPoint N z a| ≤ S.a r/4) :
    let T := center S p h 0
    wrap (S.side N p) z ∈ T.margin 0 (Cells.span S h p/5) := by
  intro T
  let D := S.toDepth h p
  let d := Cells.span S h p
  let y := wrap (S.side N p) z
  have ho : Odd d := S.toDepth_odd h p
  have hd : 0 < d := D.count.property
  have he : S.a r = S.a N*d := (S.embeds_scale D).symm
  let j (i : Axis) := ((d/2:ℕ):ℤ)+z i
  have hj i : 0 ≤ j i ∧ (d/5:ℕ)≤(j i).toNat ∧ (j i).toNat+d/5<d := by
    have hz : |S.a N * ↑(z i)| ≤ S.a r/4 := H i
    have hM : (|z i|:ℤ)*4≤ (d:ℤ) := by
      apply (show (((|z i|:ℤ)*4:ℤ):ℝ) ≤ (((d:ℕ):ℤ):ℝ) → _ from fun w => by exact_mod_cast w)
      push_cast
      rw [he,abs_mul,abs_of_pos (S.a_pos _)] at hz
      apply le_of_mul_le_mul_left _ (S.a_pos N); linarith
    have := le_abs_self (z i)
    have := neg_abs_le (z i)
    dsimp only [j]; obtain ⟨q,hq⟩ := ho; omega
  have hD : d < (S.side N p).val := T.narrow
  have hx (i : Axis) : T.coordinated 0 y i = (j i).toNat := by
    have hp : (j i).toNat < d := (Nat.le_add_right ..).trans_lt (hj i).2.2
    have hE : y i-T.starts 0 i=(((j i).toNat:ℕ):Per (S.side N p)) := by
      rw [T.starts_zero]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hj i).1]
      dsimp only [j]; rw [Int.cast_add, Int.cast_natCast]
      change (↑(z i): Per _) - (0-((d/2:ℕ):Per _))=_
      abel
    rw [Tiling.coordinated,hE, ZMod.val_natCast_of_lt (hp.trans hD)]
  refine ⟨?_,?_⟩
  · intro i; change T.coordinated 0 y i < d
    rw [hx]; exact (Nat.le_add_right ..).trans_lt (hj i).2.2
  intro i
  change d/5≤T.coordinated 0 y i ∧ T.coordinated 0 y i+d/5+1≤d
  rw [hx]; exact (hj _).2

def Comfortable (r k : ℕ) (p : Cover) := ∀ a, |S.gridPoint k p a| ≤ S.a r/4

lemma lifted {k N p} (h : k ≤ N) (x : Cover) :
    location S k N p x=wrap _ ((S.toDepth h p).count.val • x) ∧
    S.gridPoint N ((S.toDepth h p).count.val • x) = S.gridPoint k x := by
  refine ⟨?_,?_⟩
  · rw [location,dif_pos h,Ratio.embed_wrap]
  apply PiLp.ext; intro i
  simp only [Schedule.gridPoint,WithLp.ofLp_toLp, Pi.smul_apply,nsmul_eq_mul,Int.cast_mul, Int.cast_natCast,←mul_assoc,S.embeds_scale]
lemma margin {r k N p} (he : r≤k) (hk : k≤N) (x : Cover) (h : Comfortable S r k x) :
    let T := center S p (he.trans hk) 0
    location S k N p x ∈ T.margin 0 (Cells.span S (he.trans hk) p/5) := by
  rw [(lifted S hk x).1]; refine halfFit S _ _ fun i => ?_
  rw [(lifted S hk x).2]; exact h i

lemma rootTransport {r k N p} (he : r≤k) (hk : k≤N) (i : Site (S.side r p)) :
    (S.toDepth hk p).embed ((S.toDepth he p).embed i)=(S.toDepth (he.trans hk) p).embed i := by
  let A := S.toDepth hk p
  let B := S.toDepth he p
  let D := S.toDepth (he.trans hk) p
  have hh : ((S.toDepth hk p).count.val*(S.toDepth he p).count.val)=(S.toDepth (he.trans hk) p).count.val := by
    have ht : (A.count.val : ℝ)*(B.count.val : ℝ)= D.count.val := by
      apply mul_left_cancel₀ (S.a_pos N).ne'
      rw [←mul_assoc,S.embeds_scale A,S.embeds_scale B,S.embeds_scale D]
    exact_mod_cast ht
  rw [Ratio.embed,B.lift_embed,Ratio.embed,smul_smul,hh]



-- Parent really indexes these chambers.
lemma ownChamber {r N p : ℕ} (h : r ≤ N) (v : Site (S.side r p)) (x : Site (S.side N p)) :
    x∈(center S p h 0).chamber v ↔ (S.toDepth h p).parent x=v := by
  let D := S.toDepth h p
  let T := center S p h (0 : Site (S.side N p))
  obtain ⟨⟨w,y⟩,rfl⟩ := D.assemble_bijective.2 x
  change D.assemble (w,y)∈T.chamber v ↔ D.parent (D.assemble (w,y))=v
  rw [D.assemble_parent]
  suffices H : D.assemble (w,y)∈T.chamber w by
    refine ⟨fun hx => (T.which_chamber H).symm.trans (T.which_chamber hx), fun hv => hv ▸ H⟩
  intro i
  let a := lift y
  have he := lift_centers y i
  have hh : Odd D.count.val := S.toDepth_odd h p
  let d := D.count.val
  let b : ℤ := a i+((d/2:ℕ):ℤ)
  have hp : 0 ≤ b ∧ b.toNat < d := by obtain ⟨w,h⟩ := hh; unfold b d a; omega
  have ht : d < (S.side N p).val := T.narrow
  have hk : D.assemble (w,y) i-T.starts w i= ((b.toNat:ℕ):Per _) := by
    change (D.embed w i + ((a i : ℤ) : Per (S.side N p))) - ((0-((d/2:ℕ):Per _)) + D.embed w i)=_
    rw [← Int.cast_natCast (R:= Per _) b.toNat, Int.toNat_of_nonneg hp.1]
    unfold b; rw [Int.cast_add,Int.cast_natCast]; abel
  change (D.assemble (w,y) i-T.starts w i).val < d
  rw [hk,ZMod.val_natCast_of_lt (hp.2.trans ht)]; exact hp.2

lemma via_layers {r k N p} (hr : r≤k) (hk : k≤N) (x : Site (S.side N p)) :
    (S.toDepth hr p).parent ((S.toDepth hk p).parent x)=(S.toDepth (hr.trans hk) p).parent x := by
  let A := S.toDepth hk p
  let B := S.toDepth hr p
  let D := S.toDepth (hr.trans hk) p
  obtain ⟨⟨s,t⟩,rfl⟩ := A.assemble_bijective.2 x
  obtain ⟨⟨w,u⟩,rfl⟩ := B.assemble_bijective.2 s
  let y := A.assemble (B.assemble (w,u),t)
  let z : Cover := A.count.val • lift u + lift t
  have ht : A.count.val * B.count.val=D.count.val := by
    have hu : (A.count.val : ℝ)*(B.count.val : ℝ)= D.count.val := by
      apply mul_left_cancel₀ (S.a_pos N).ne'
      rw [← mul_assoc,S.embeds_scale A,S.embeds_scale B,S.embeds_scale D]
    exact_mod_cast hu
  have he : lift (wrap D.count z) = z := by
    apply lift_eq_iff.mpr; refine ⟨rfl,fun i => ?_⟩
    have hA := lift_centers t i
    have hB := lift_centers u i
    rw [← ht]
    dsimp only [z]; rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]; push_cast
    let a : ℤ := lift t i
    let b : ℤ := lift u i
    change -( (A.count.val:ℤ)*(B.count.val:ℤ)) < 2*((A.count.val:ℤ)*b+a) ∧ _
    have hq : 0 < (A.count.val:ℤ) := by exact_mod_cast A.count.property
    constructor
    · have hL : - (B.count.val:ℤ)+1 ≤ 2*b := hB.1
      have hT : - (A.count.val:ℤ) < 2*a := hA.1
      linarith only [mul_le_mul_of_nonneg_left hL hq.le,hT]
    have hw : 2*b < (B.count.val:ℤ) := Ratio.unambiguous (S.toDepth_odd hr p) u i
    change 2*((A.count.val:ℤ)*b+a) ≤ _
    have hT : 2*a ≤ A.count.val := hA.2
    linarith only [mul_le_mul_of_nonneg_left (show 2*b + 1 ≤ (B.count.val:ℤ) from hw) hq.le,hT]
  have H : y = D.assemble (w,wrap _ z) := by
    change A.root (B.embed w+wrap _ (lift u))+wrap _ (lift t) = D.embed w+wrap _ (lift _)
    rw [he,map_add,A.root_embed,A.root_embed, A.embed_wrap]
    rw [show A.embed (B.embed w)=D.embed w from rootTransport ..,add_assoc]
    rw [show z= _ + lift t from rfl,(wrap _).map_add]
  rw [A.assemble_parent,B.assemble_parent]; change w=D.parent y; rw [H,D.assemble_parent]

lemma parentCopy {r k N p} (he : r≤k) (hk : k≤N) (x : Cover) (h : Comfortable S r k x) :
    let T := center S p (he.trans hk) 0
    ∀ i : Site (S.side r p), (S.toDepth (he.trans hk) p).parent (T.copyMap i (location S k N p x)) = i := by
  intro T i; refine (ownChamber S (he.trans hk) i _).1 (T.enumerate i ?_)
  exact (margin S (p:=p) he hk x h).1
lemma generous (r M : ℕ) : ∀ᶠ N : ℕ in atTop, ∃ h : r ≤ N, ∀ p, M≤ Cells.span S h p/5 := by
  have he := S.shrinks.const_mul (M*5+1:ℝ)
  rw [mul_zero] at he
  filter_upwards [eventually_ge_atTop r,he.eventually (gt_mem_nhds (S.a_pos r))] with N h hv
  refine ⟨h,fun p => ?_⟩
  have hp : (↑M*5+1:ℝ)*S.a N < _ := hv
  rw [← S.embeds_scale (S.toDepth h p),mul_comm (S.a N)] at hp
  have ht := lt_of_mul_lt_mul_right hp (S.a_pos N).le
  have hz : M*5+1 < (S.toDepth h p).count.val := by exact_mod_cast ht
  unfold Cells.span; omega
end AnyGeom

section Physical
variable {G : Gauge} {C : Family G}

lemma stencil (d r : ℕ) : ∀ᶠ N : ℕ in atTop, ∀ p k : ℕ, ∀ x : Cover,
    ∀ (he : r≤k) (hk : k≤N), Comfortable C.S r k x →
      ((C.localSection d).footprint (location C.S k N p x) : Set _) ⊆
        (center C.S p (he.trans hk) 0).chamber 0 := by
  let l := (C.localSection d).stencil
  let M := l.sup (fun z => Finset.univ.sup fun i => (z i).natAbs)+1
  have hm z (hz : z ∈ l) a : (z a).natAbs < M := Nat.lt_succ_of_le <|
    le_trans (Finset.le_sup (s:=Finset.univ) (f:=fun i => (z i).natAbs) (Finset.mem_univ a)) (Finset.le_sup (f:=fun z : Cover => Finset.univ.sup fun i => (z i).natAbs) hz)
  filter_upwards [generous C.S r M] with N hn
  intro p k x he hk hx y hy
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
  exact Tiling.fits_stencil _ (margin C.S he hk x hx) (fun a => (hm w hw a).trans_le ((hn.choose_spec) p))

lemma interior (H : C.Makes) (d r : ℕ) : ∀ᶠ N : ℕ in atTop,
    ∀ p k : ℕ, ∀ x : Cover, ∀ (he : r≤k) (hk : k≤N), Comfortable C.S r k x → ∀ v : C.label d,
      Interior ((center C.S p (he.trans hk) 0).chamber 0)
        (C.O N p (d:=d) v (location C.S k N p x)) := by
  filter_upwards [stencil (C:=C) d r] with N hn
  intro p k x he hk hx v
  let F := C.O N p v (location C.S k N p x)
  have hf : Continuous F := C.continuousO ..
  refine ⟨C.invariant H _ _ _ _ _,hf.measurable,?_, hf.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
  intro U Z h; exact (C.localO _ _ _ _ _) U Z (agrees_mono h (hn p k x he hk hx))

/-- Fixed cell points fit in p for every period. -/
lemma hosted {n k r : ℕ} (p : ℕ) (x : Fin n → Cover) (h : ∀ i, Comfortable C.S r k (x i)) :
    Extraction.Order.grid C k x∈ Inside C.S p _ := by
  have hu : C.S.a r ≤ 1 := (C.S.strictAnti.antitone (Nat.zero_le r)).trans (C.S.a_zero.le)
  have he : (1:ℝ) ≤ (C.S.period p).val := by exact_mod_cast (C.S.period p).property
  intro i a
  specialize h i a
  apply abs_lt.mp
  change |C.S.gridPoint k _ a|< C.S.radius _
  unfold Schedule.radius
  linarith
end Physical
end YM.Push.Corrected.Positions
