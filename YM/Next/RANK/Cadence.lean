import YM.Next.RANK.Currents
import YM.Next.RANK.Joints
import YM.Next.RANK.Starring

/-!
# Boot to march of W

Start with all the fields of Lit.Contour, ready for repeated transfer, even
if some W has zero coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Cells Station Ac Alarm Thirst Corona Value Finset MeasureTheory Edition Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {B : Side}
variable {S : Schedule} {C : Family G} {A : Levels G} {i k l j m p q D N d n a : ℕ}
variable {c r s ε e v : ℝ}

-- Geometry estimates. May use orders and supports only on comparison arcs.
structure ReadySh (s : ℝ) (X : AtlasData G A.S p) (d q k : ℕ) (R : Lead G A.S p) : Prop where
  canvas : roomTest A s k p d q
  withers i : middle A s k ≤ i → i<k → Mote (A:=A) R i
  gauge i : middle A s k ≤ i → i<k → Voice R i

variable {Y : AtlasData G C.S p} {F : Lead G C.S p}
variable (x : Points n) (P : Fin n→ C.label d)

def jacketPol {Q} (M : StampDuty C k N p d D Q q Y) (hk : i≤k) := polygon F (fun i=> prefaced M (P i) (Station.choose C.path.levels s k x i)) hk

-- h per stamp; same H and W clipping parameters for Gauge
section
variable {Q : Rep G (C.side k p)}
variable (M : StampDuty C k N p d D Q q Y) (R : ReadySh (A:=C.path.levels) s Y a q k F)

lemma primed (i : Fin n) (s : ℝ) (f) (hp : f∈ (prefaced M (P i) (Station.choose C.path.levels s k x i)).vars):
    fog C.path.levels x s p 8 (walls (clim C.path.levels k)) le_rfl i f:= by
  unfold prefaced at hp; rw [primeVisit] at hp; obtain ⟨j,hj,rfl⟩:= mem_vars_rename _ _ hp
  let A:= C.path.levels; let w:= Station.choose A s k x i; let o:=wrap (C.side k p) w
  change separation (core A x s p (show k≤k from le_rfl) i) (wrap (C.side k p) (w+j.1.val.1)) ≤ sizeQ C k
  rw [homeHere]; rw [map_add,add_comm]; exact Work.E08.separation_box_add _ (faceOrigin _)

-- strong for all pennants, not just Cozy
include R
lemma premise (hk : i≤ k) (H : middle C.path.levels s k ≤ i) (j : pennant n) :
    let P:=jacketPol (F:=F) (s:=s) x P M hk j
    Poetic P ∧ ∀ f∈P.vars, spotP (C:=C) s i a hk x j f:= by
  intro W; unfold W jacketPol; let A:=C.path.levels; let q:=fun i=>prefaced M (P i) (Station.choose A s k x i)
  refine ⟨verses _ _ hk (fun i h=> R.gauge i (H.trans h)) (fun i=> ?_) j,?_⟩
  · unfold prefaced; rw [primeVisit]; exact poetry _ (M.crystal _) _ _
  intro f hh; cases j with
  | inl b=> exact le_trans (axis_room x F q R.canvas H R.withers (fun i j=>primed x P M i s j) hk b _ hh) (Nat.mul_le_mul_right _ (Nat.le_add_left ..))
  | inr b=> exact (pole_room x F q R.canvas H R.withers (fun i j=>primed x P M i s j) hk b).2 _ hh
lemma falters (hk : i≤k) (H : middle C.path.levels s k ≤ i) (j : Twin n) : ¬cozy C.path.levels x s p a (walls (clim C.path.levels i)) hk (.inr j) → jacketPol (F:=F) (s:=s) x P M hk (.inr j)=0:= (pole_room x F _ R.canvas H R.withers (fun i j=>primed x P M i s j) hk j).1

def mimics (hN : k≤N) (hk : i≤k) (hi : middle C.path.levels s k ≤ i) (c : ℝ) (L : Lane C k s p a x hk):= mimic x s p hN hk hi R.canvas L _ c (premise x P M R hk hi _).2 (premise x P M R hk hi _).1

-- Initial W payload costs transferred unchanged, path transformations from Truth

omit R in
private lemma signet_here {n : Side} (o : Site n) (j : ℝ) (P : Normal.poly (slotC G k)) (U : Config G n) : signet o j P U=signet 0 j P (pull 1 o U):= by
  unfold signet Spindle.curl registered; rw [s_translation]
lemma journey (hN : k≤N) (j : Fin n) (v : (Ship.yard C s hN p).Cell) (g : ℝ) (U : Config G (C.side k p)) :
    let A:= C.path.levels
    glory (C:=C) x s p hN le_rfl (before A s k) v (.inl j) g (jacketPol (s:=s) (F:=F) x P M le_rfl (.inl j)) U= dot ((Ship.yard C s hN p).hand v)
      (signet 0 g (M.W (P j)) (pull ((Ship.yard C s hN p).omega v) (seats C s x hN p (v,j)) U)):= by
  intro A; simp only [glory, Function.comp_apply,jacketPol,polygon,oneRoot,center_shelf]
  let T:=Ship.yard C s hN p; let l:middle A s k≤k:=before ..; let a:= (Station.wider A s k).trans l; let u:= wrap (C.side k p) (Station.choose A s k x j)
  have hx : seats C s x hN p (v,j)= affine (T.omega v) (spreadC C s p a v) u:= by
    let y:=core A x s p (k:=k) le_rfl j
    have hv:y=u:=homeHere ..; rw [← hv]; exact fills C x s p hN le_rfl a _
  have hp : 8 ≤ q:= by linarith only [R.canvas.radius]
  unfold prefaced; rw [show core C.path.levels x s p le_rfl (headMark (Sum.inl j))=u from homeHere .., caseK Y _ k _ M.r g _ ?_, signet_here u, watches,pull_pull,mul_one,hx]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ hp) _)) (R.canvas.suite k l le_rfl)
end

section
variable {n : Side} {V ι κ : Type} [Fintype V] [DecidableEq V]
private lemma basicLight {ζ : V→ Site n} [Fintype ι] [Fintype κ] {r : V→ℝ} {h k e₀ : ℝ} (L : Rep G n) {A : ι→ SourceAt G ζ} {K : κ→ Lifted G ζ L.p.threshold} (H : Unpacks A L.p r e₀ h) (ht : prepared (q:=L.p) K r e₀ k) : Light L A K r e₀ h k:= by
  obtain ⟨m,hm,h⟩:=H; obtain ⟨p,hp,hk⟩:=ht; constructor
  · refine ⟨fun i=>m i*Value.charge L.p e₀ (A i).extent, fun i=>⟨mul_nonneg (hm i|>.1) (Real.exp_pos _).le,fun U hx=>?_⟩, fun i=>?_⟩
    · rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left (((transferD ..).mp (hm i)).2 _ hx) (Real.exp_pos _).le).trans_eq (mul_comm ..)
    simpa [Value.charge] using! (sum_pay _ _ _ (fun i=>mul_nonneg (hm i|>.1) (Real.exp_pos _).le)).1 (h i)
  refine ⟨fun i=>p i*Value.charge L.p e₀ (K i).extent, fun i=>⟨mul_nonneg (hp i|>.1) (Real.exp_pos _).le,fun U=>?_⟩,fun i=>?_⟩
  · rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left ((hp i).2 U) (Real.exp_pos _).le).trans_eq (mul_comm ..)
  simpa [Value.charge] using! (sum_pay _ _ _ (fun i=> mul_nonneg (hp i|>.1) (Real.exp_pos _).le)).1 (hk i)

end
-- Stamp


def marche (s : ℝ) (hN : k≤N) (h : i≤k) (Q : Rep G (C.side i p)) (c : Course C N p k) (x : Points n) (P : Fin n→ C.label d)
    (a : ℕ) (W : Lane C k s p a x h → SourceAt G (readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN))) (r e v η : ℝ): Prop :=
    let S:= Issued C s x hN p P
    ∃ (ι κ : Type),∃ (_ : Fintype ι) (_ : Fintype κ), ∃ H : ι→SourceAt G (readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN)),∃ K : κ→ Lifted G (readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN)) Q.p.threshold,
      c.flow S i (h.trans hN)= Value.dust Q (Sum.elim H W) K ∧ Background Q K ∧ Light Q H K (fun _=>r) e v η

theorem marched (hN : k≤N) (c : Course C N p k) {Q : Rep G (C.side k p)} (M : StampDuty C k N p d D Q q Y) (R : ReadySh (A:=C.path.levels) s Y a q k F)
    {η} (x : Points (m+1)) (P : Fin (m+1)→ C.label d) (hQ : Q.p.B= walls (clim C.path.levels k))
    (h : Rod m x s hN P c Q (kicks P M s hN (Q₀:=x)) e r v η) :
    let W:= mimics x P M R hN le_rfl (before _ _ _) (LiftMark.GaugeScale C k N p)
    marche s hN le_rfl Q c x P a W r e v η:= by
  intro W; obtain ⟨ι,κ,ha,hb,H,K,hL,hB,hT,hw⟩:= h
  let A:= C.path.levels; let α:= Listens C s (v:=m+1) hN p; let β:=Lane C k s p a x le_rfl; let V : α→_:= kicks P M s hN (Q₀:=x); let F (t:α) : β:= ⟨t.1,soloIndex x s A p a le_rfl t.2⟩
  refine ⟨ι,κ,ha,hb,H,K,hL.trans ?_,hB,basicLight _ hT hw⟩
  ext1 U; unfold dust; rw [Fintype.sum_sum_type,Fintype.sum_sum_type]; congr 3;
  let b:= Q.p.threshold
  have he (t : α):(W (F t)).amount b U=(V t).amount b U:= by
    have hx : (W (F t)).extent=(V t).extent:= by
      change Spindle.patch (q*walls (clim C.path.levels k)) _=swath (hand C s hN p t) (seats C s x hN p t) (halo (q*Q.p.B) {0}); rw [swath_iffHalo,hQ]; simp only [swath,image_singleton,affine,Signed.act_zero,zero_add]; rfl
    have hv:(W (F t)).fires=(V t).fires:= by
      apply Subtype.ext; change {t.1} ×ˢ ({t.2}: Finset _)={t}; rw [singleton_product_singleton]
    have hh:(W (F t)).value=(V t).value:=funext fun u=>journey x P M R hN t.2 t.1 _ _
    rw [SourceAt.amount,SourceAt.amount,hx,hv,hh]
  apply congr_arg ((∑ i, (H i).amount Q.p.threshold U)+·)
  change (∑ i,(V i).amount b U)=∑ i,(W i).amount b U
  let X:=(univ (α:=α)).image F
  have ht : Injective F:=fun i j h=> by
    refine Prod.ext (show (F i).1=(F j).1 from congr_arg Prod.fst h) ?_
    exact Sum.inl.inj (congr_arg (fun x:β=> x.2.val) h)
  rw [← sum_subset (subset_univ X) ?_, sum_image ht.injOn]; simp_rw [he]
  intro i _ hh
  rcases i with ⟨x,⟨y|z,hb⟩⟩
  · exact False.elim (hh (mem_image.mpr ⟨(x,y), mem_univ _,rfl⟩))
  let Z:β:=(x,⟨Sum.inr z,hb⟩)
  change Poly.send (W Z).fires (masked b (W Z).extent (W Z).value U) = _
  by_cases hz: Healthy b (W Z).extent U
  · rw [masked_eq b _ _ _ hz]
    simp only [W, mimics,mimic,glory,caseW,Function.comp_apply,Z,jacketPol,polygon,twoRoot,oneRoot,center_shelf,sub_self,text,map_zero,Edition.dot_zero,Poly.send_zero]
  rw [masked_ne _ _ _ _ hz, Poly.send_zero]
end YM.Next.Rank.Tapes
