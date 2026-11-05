import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rhyme

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "za'" => za M H (n:=n)
variable {t Y₁ g z c₁ v₁ b₁ κ' e:ℝ}
variable (h: Herd H N.conduit A B n)
open Next.Foundations
variable (χ' : Chi)
lemma theme (m:Molecule S)(hi: ¬ troupe T R Q.halo (radiusB x) m) : escort M χ' Q.table m Q.halo T W x o.K o.a=0:=by
  letI:Nonempty (Tree.Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  funext i; unfold escort Leaf.picture Leaf.grove; refine Eq.trans ?_ (likely_constant (A:=Greenbelt.Reserve S) 0)
  apply congr_arg likely; funext j; apply integral_eq_zero_of_ae; filter_upwards with z; exact if_neg (fun h=>hi h.2)
lemma sunset (m:Molecule S)(hi: M.turn.badge S∉m) : escort M χ' Q.table m Q.halo T W x o.K o.a=0:=by
  letI:Nonempty (Tree.Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  funext i; unfold escort; refine Eq.trans ?_ (likely_constant (A:=Greenbelt.Reserve S) 0); apply congr_arg likely; funext j; exact stalk M _ hi

def chip (P : H.ThinP) : H.fragrances:=⟨0,fun _=> P⟩

lemma single (p:H.fragrances)(h:p.1=0): p=chip H (p.snd none):=by rcases p with ⟨k,f⟩; change k=0 at h; subst k; unfold chip; congr 1; funext i; rw [Subsingleton.elim i none]
lemma clipS (p : H.ThinP): H.bookFoot (.inr (chip H p))=H.unionP p.val:=by change unionOf _ _ =_; unfold chip unionOf; ext i; simp only [mem_biUnion]; exact ⟨fun ⟨_,_,hh⟩=>hh, fun h=>⟨none,mem_univ _,h⟩⟩
lemma chip_m (χ : Chi) (p : H.ThinP) : matin M H (chip H p) χ=escort M χ Q.table p.val Q.halo T W x o.K o.a:=by
  funext v; unfold matin chip; dsimp only
  have ht {Z : H.ThinP} : coefficient H.seam (fun _: Option (Fin 0)=> Z)=1 := by
    unfold coefficient
    let v : Option (Fin 0) → H.ThinP:=fun _=>Z
    have he : pot H.seam v=∅:= by
      apply Finset.eq_empty_iff_forall_notMem.mpr; intro p hp; have h:= (potential_mem H.seam v p |>.mp hp).1
      have hv : p.card ≤ 1:= (Finset.card_le_univ _).trans (by simp); omega
    change Graph.mass (pot H.seam v)=1; rw [he]; unfold Graph.mass; have hh : Graph.reaches (∅: Graph.Network (Option (Fin 0))) := by
      intro i j; rw [Subsingleton.elim i j]
    have he : Graph.connectedGroups (∅:Graph.Network (Option (Fin 0)))={∅}:= by ext i; simp only [Graph.belongs,Finset.subset_empty,Finset.mem_singleton]; exact ⟨And.left,fun e=> e.symm ▸ ⟨rfl,hh⟩⟩
    rw [he]; simp [Graph.alternating]
  rw [ht]; simp; rfl

def speaks (r:H.fragrances):Prop:=∃ i,M.turn.badge S∈(r.2 i).val ∧ troupe T R Q.halo (radiusB x) (r.2 i).val
-- no multiplicity choice
lemma quiet (r:H.fragrances)(hs:¬speaks M H r):matin M H r χ'=0:=by
  funext V; unfold matin; rw [Finset.sum_eq_zero,mul_zero]; rfl
  intro i hi; obtain hx:=fun h=> hs (show speaks M H r from ⟨i,h⟩); rcases not_and_or.mp hx with ht|ht
  · rw [libs,show escort M χ' Q.table (r.2 i).val Q.halo T W x o.K o.a V=0 from congr_fun (sunset M χ' (r.2 i).val ht) V,mul_zero] -- implicits.N.V
  rw [libs, show escort M χ' Q.table (r.2 i).val Q.halo T W x o.K o.a V=0 from congr_fun (theme M χ' (r.2 i).val ht) V,mul_zero]
-- Principal candidate (E-only cannot mandatory).
def prince (r : H.fragrances) := r.1=0 ∧ (r.2 none).val={M.turn.badge S} ∧ troupe T R Q.halo (radiusB x) (r.2 none).val
-- output support counting.No coe.Site.
def locus (y:Site c) (r:H.fragrances): Support c:= if speaks M H r then H.bookFoot (.inr r) else {y}
lemma seatY (y:Site c)(hp : y∈ M.crest.image S.ratio.parent)(r:H.fragrances): y∈locus M H y r:=by
  unfold locus; split; next h=> obtain ⟨i,hv,_⟩:=h; apply (show H.unionP (r.2 i).val⊆ H.bookFoot (.inr r) from subset_biUnion_of_mem (H.smallAt ∘ r.2) (mem_univ i)); apply (show areas R T Q.halo (radiusB x) (M.turn.badge S)⊆_ from subset_biUnion_of_mem _ hv); rw [M.turn.badge_area]; apply halo_subset; exact image_subset_image (show M.crest⊆ RG.inspected M.crest from subset_union_left) hp
  next=> exact mem_singleton_self _
lemma mask_ag (r:H.fragrances)(V:Config G c)(t:ℝ)(x:Site c): masked t (locus M H x r) (matin M H r χ') V=masked t (H.bookFoot (.inr r)) (matin M H r χ') V:=by
  unfold locus; split; · rfl
  next h=>
    have hk:=quiet M H χ' r h; rw [hk]
    unfold masked; simp
variable (U : BudgetPoint)(hu: U.threshold=Pressure.temp x)(hf: U.order≤j)
-- reusable leaf-to-Orb
def flareC (p : ℕ)(X : Support c) := (shiftG x*(1+coverNumber (radiusB x) X))^(p*j) -- typo ℝ coe
include h hu hf
lemma adapted (y:Site c)(p:H.fragrances)(hy:y∈ H.bookFoot (.inr p)):
    let X:= H.bookFoot (.inr p)
    U.Regular X (matin M H p χ) ∧ U.supBounds y X (matin M H p χ) (d0*oval M H N p*flareC (x:=x) (j:=j) U.power X):=by
  intro Z; let b:ℝ:=d0*oval M H N p; let q :ℝ:=coverNumber (radiusB x) Z; let f:=matin M H p χ
  obtain ⟨hx,hY,hF,h'⟩ := heeds M H N h p
  have hL V (hh : Healthy U.threshold Z V) : Ore V f v b j:= h' V (hu ▸ hh)
  have hh V (ht : Healthy U.threshold Z V) : ContDiffAt ℝ (↑U.order) (f ∘ increment V) 0 := (charted (hL V ht) N.position).of_le (Nat.cast_le.mpr hf)
  have hhU : Sailor G U.threshold C' j:= ⟨fun c _ hb=> N.weigh.stroke c _ (hb.trans (hu.trans_le N.talent))⟩; let t:ℝ:= shiftG x * (1+q)
  have hb:=mul_nonneg (dew M H|>.2.1) (oval_pos M H N p)
  have hs:1≤ shiftG x:=by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
  have hi:1≤t:=one_le_mul_of_one_le_of_one_le hs (le_add_of_nonneg_right (Nat.cast_nonneg _))
  refine ⟨⟨hx,hY,hF,hh,fun V h A l hl=>left_has A hl (hh V h)⟩,mul_nonneg hb (pow_nonneg (zero_le_one.trans hi) _),fun V ht l hl hs=>?_⟩
  apply (costsD (g:=f) hx hhU N.income y _ N.near (hL V ht) (Y:=t) ?_ hi l (hl.trans hf) hs).trans_eq; · exact mul_comm ..
  intro i he; have hf : (separation i y:ℝ) ≤ q*(4*(radiusB x:ℝ)+2)+2*(radiusB x:ℝ) := by unfold q; exact_mod_cast Lattice.Corona.extent Z (radiusB x) he hy
  unfold t shiftG; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x), show 0≤ q from Nat.cast_nonneg _]
end Charity
end YM.PhysicalNext.Repeat.Daisy
