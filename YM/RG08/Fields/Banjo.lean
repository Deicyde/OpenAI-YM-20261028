import YM.RG08.Fields.Warp
import YM.Next.FREE_KERNELS.Current

/-! # Shared Frost: absolute and overlapping gauges and metrics.
The Hölder exponents on these auxiliaries are not used to reset the
interaction grade constants (those run directly on K and the Tree). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08
open Stationary
open scoped Topology BigOperators
variable {j n : ℕ} {k : ℝ}

structure Chords (A B : ℝ) {ι ζ : Type} (U V : Row ι ζ) (s : ℝ) : Prop where
  high : U.strip s A
  low : V.strip s A
  mov : (minusRows U V).strip s B
namespace Chords
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] {P Q : Row α β} {M N : Row β γ} {X D A B u s t x : ℝ}
omit [Fintype α] [Fintype γ] in
lemma frame (hP : Chords A B P Q s) (hM : Chords u t M N s) (hs : 0<s) :
    Chords ((Fintype.card β : ℝ)*(A*u)) ((Fintype.card β : ℝ)*(A*t)+(Fintype.card β : ℝ)*(B*u))
      (composeRows P M) (composeRows Q N) s := by
  let I:= composeRows P M; let J:=composeRows Q N; let V:=composeRows P (minusRows M N); let U:=composeRows (minusRows P Q) N
  have ha : Whole P := ⟨_,_,hs,hP.high⟩; have hb : Whole Q:=⟨_,_,hs,hP.low⟩
  have hc : Whole M := ⟨_,_,hs,hM.high⟩; have hd : Whole N:=⟨_,_,hs,hM.low⟩
  refine ⟨strip_compose hs.le hP.high hM.high,strip_compose hs.le hP.low hM.low,?_⟩
  rw [show minusRows I J=plusRows V U from bank_injective ((ha.prod hc).minus (hb.prod hd)).safe
      ((ha.prod (hc.minus hd)).plus ((ha.minus hb).prod hd)).safe (fun i=> by
        unfold I J V U
        rw [(ha.prod hc).less (hb.prod hd), (ha.prod (hc.minus hd)).acts_plus ((ha.minus hb).prod hd),ha.acts hc,hb.acts hd, ha.acts (hc.minus hd),(ha.minus hb).acts hd,
          ha.less hb,hc.less hd,Matrix.mul_sub,Matrix.sub_mul]; abel)]
  have hh := strip_minus (strip_compose hs.le hP.high hM.mov) (strip_scale (strip_compose hs.le hP.mov hM.low) (-1))
  simpa only [norm_neg,norm_one,one_mul,plusRows,V,U] using hh
omit [Fintype α] [Fintype β] in
lemma tack (hf : Chords A B P Q s) (hl : t≤s) (hA : A ≤ X) (hB : B≤D) : Chords X D P Q t :=
    ⟨strip_mono hf.high hl hA,strip_mono hf.low hl hA,strip_mono hf.mov hl hB⟩
omit [Fintype α] [Fintype β] in
lemma nativeCh (L : Side) (h : Chords A B P Q s) (hs : 0<s) :
    Chords (Real.exp (4*s)*A) (Real.exp (4*s)*B) (nativeRow L P) (nativeRow L Q) s :=
    have hp : s ≤ L.val*s := le_mul_of_one_le_left hs.le (by exact_mod_cast L.property)
    ⟨native_price h.high hs.le hp,native_price h.low hs.le hp,native_price h.mov hs.le hp⟩
end Chords

lemma psi_nurture (k : ℝ) (hk : 0<k) (S : Flight j n) (hn : 4 ≤ n) :
    Flight.psi k S=composeRows (composeRows (nativeRow S.L (blue k S.wing)) (S.duo k).T) (pink k S.land) := by
  have hv := heart_h hk S.legal S.wing; have hm:=heart_h hk hn S.land
  have hh:Whole (Flight.psi k S):= (Flight.paid_path_stock k hk S.legal hn (u:=[]) (Nat.zero_le _)).whole S
  have hg:= ((Flight.budgets_linear k hk S.legal hn).2).whole S
  have ht := native_whole S.L hv.2
  refine bank_injective hh.safe ((ht.prod hg).prod hm.1).safe fun c=> ?_
  let f : Side:= c*S.L; let g:= S.visitRatio (c:=c) (f:=f) rfl
  have hp (α : Type) [Fintype α] [DecidableEq α] (β : Type) [Fintype β] [DecidableEq β] (R : Cross S.L α β) :
      R.acts c=repackM (splitCo g α) (Equiv.refl _) (installed g R) := by
    ext i j; obtain ⟨i,rfl⟩:= (splitCo g α).surjective i; simp only [repackM,Matrix.submatrix_apply,Equiv.symm_apply_apply]; rfl
  rw [(ht.prod hg).acts hm.1,ht.acts hg,hp _ _ _]
  rw [show installed g _ = _ from S.psi_bridge k hk hn (c:=c) (f:=f) rfl, repack_multiply _ (Equiv.refl _),repack_multiply _ (splitCo g _), ← hp _ _ ((S.duo k).T)]
  erw [← native_acts g hv.2]; rfl

lemma crayon {σ s c : ℝ} (_ : 0<s) (hc : 0≤c) (F : Frost k j σ s c) (A B : Train j) {X:ℝ} (hX : 0≤ X)
    (hu : (minusRows (hessian (pink k A)) (hessian (pink k B))).strip σ (X^26)) :
    let C:=c+c
    Chords c (C*X) (pink k A) (pink k B) s ∧ Chords c (C*X) (blue k A) (blue k B) s := by
  intro C
  have hg (u v : Row (TypeFace 2) (TypeFace 2)) (ha : u.strip s c) (hb : v.strip s c) (he : (minusRows u v).strip s (X^26*c)) : Chords c (C*X) u v s := by
    refine ⟨ha,hb,?_⟩
    by_cases he': X≤1
    · refine strip_mono he le_rfl ?_
      rw [mul_comm (X^26)]; exact mul_le_mul (le_add_of_nonneg_right hc) (by simpa only [pow_one] using (pow_le_pow_of_le_one hX he' (by decide : 1 ≤ (26:ℕ)))) (pow_nonneg hX _) (add_nonneg hc hc)
    exact strip_mono (strip_minus ha hb) le_rfl (le_mul_of_one_le_right (add_nonneg hc hc) (not_le.mp he').le)
  have hw := F.lift (X^26) A B (pow_nonneg hX _) hu
  exact ⟨hg _ _ (F.hue A).1 (F.hue B).1 hw.1, hg _ _ (F.hue A).2 (F.hue B).2 hw.2⟩

/-- Outputs retain a width positive before L. Constants C in addition
    are width costs, may be stipulated at a stage. One fixed exponent. -/
structure Stairs (S : Flight j n) (k σ τ α C : ℝ) : Prop where
  up (X : ℝ) (u v : Train j) : 0≤X → (minusRows (hessian (pink k u)) (hessian (pink k v))).strip σ (X^26) →
      (minusRows (hessian (pink k (flutter S u).land)) (hessian (pink k (flutter S v).land))).strip τ (X^26) →
        let P := flutter S u; let Q:= flutter S v; let A:=Flight.duo k P; let B:=Flight.duo k Q
        Chords C (C*X) A.A0 B.A0 α ∧ Chords C (C*X) A.T B.T α ∧ Chords C (C*X) (P.psi k) (Q.psi k) α
lemma before_S (hk : 0<k) (hj : 4 ≤ j) (hn : 4 ≤ n) {σ τ:ℝ} (hs : 0<σ) (ht : 0<τ) :
    ∃ α>0, ∀ S : Flight j n, ∃ C>0, Stairs S k σ τ α C := by
  obtain ⟨q,D,hq,hD,F⟩:= ((secure_both k hk hj hn).1).bankCost hj 1 (u:=[]) (Nat.zero_le _)
  obtain ⟨r,E,hr,hE,J⟩:= ((secure_both k hk hj hn).2).bankCost hj 2 (u:=[]) (Nat.zero_le _)
  obtain ⟨β,C,hβ,hC,H⟩:= possible_frost hk hj hs; obtain ⟨δ,B,hδ,hB,K⟩:= possible_frost hk hn ht
  let s:=min q r; let A:=max D E
  let α:=min (s/4) (min β δ)
  have hy : 0<s:=lt_min hq hr; have ha:0<A:=lt_max_of_lt_left hD
  have hQ : 0<α:=lt_min (div_pos hy (by norm_num)) (lt_min hβ hδ)
  have hg (u : Flight j n) : ((u.duo k).A0).strip s A∧ ((u.duo k).T).strip s A :=
    have hz : 1 ≤ (u.L.val:ℝ) := by exact_mod_cast u.L.property
    ⟨strip_mono (F u) (min_le_left ..) ((div_le_self hD.le (one_le_pow₀ hz)).trans (le_max_left ..)),
       strip_mono (J u) (min_le_right ..) ((div_le_self hE.le (one_le_pow₀ hz)).trans (le_max_right ..))⟩
  refine ⟨α,hQ,fun S=>?_⟩
  obtain ⟨c,hc,U⟩:= gearing S hk hn hs ht
  obtain ⟨z,hz,Q⟩:= ship_warp s (A+A) c hy (add_nonneg ha.le ha.le) hc.le
  let L : ℝ:= Fintype.card (Co S.L (TypeFace 2)); let g : ℝ:= Fintype.card (TypeFace 2); let f:=Real.exp (4*α)
  let u:=L*(f*C*A); let v:= L*(f*C*z)+L*(f*(C+C)*A)
  let R:=g*(u*B); let X:=g*(u*(B+B))+g*(v*B)
  let w:=max (max z A) (max R X); have hw : 0<w:= ((lt_max_of_lt_left hz).trans_le (le_max_left ..))
  refine ⟨w,hw,⟨fun y P T he U₁ U₂ =>?_⟩⟩
  intro i j' M N
  have hL : α ≤ s/4 := min_le_left ..; have hS:=hL.trans (show s/4 ≤ s by linarith)
  have hx {ι ζ : Type} [Fintype ι] [Fintype ζ] (A₁ B₁ : Row ι ζ) (h : A₁.strip s A) (h' : B₁.strip s A)
      (hp : ∀ p∈baseCube,p≠0 → ∀ i j, ‖A₁.read p i j-B₁.read p i j‖ ≤ c*y^26*rim p^12) : Chords A (z*y) A₁ B₁ α := by
    refine ⟨strip_mono h hS le_rfl,strip_mono h' hS le_rfl,strip_mono (Q _ _ _ y he (strip_minus h h') (fun p h₀ hw i j => ?_)) hL le_rfl⟩
    rw [read_less (Whole.safe ⟨_,_,hy,h⟩) (Whole.safe ⟨_,_,hy,h'⟩) h₀.1]; exact hp p h₀ hw i j
  have hM := U P T (y^26) (pow_nonneg he _) U₁ U₂
  have hm : Chords A (z*y) M.A0 N.A0 α := hx (ι:=Co S.L (TypeFace 1)) _ _ (hg i).1 (hg j').1 (fun p hs he=> (hM p hs he).1)
  have hk' : Chords A (z*y) M.T N.T α := hx (ι:=Co S.L (TypeFace 2)) _ _ (hg i).2 (hg j').2 (fun p hs he => (hM p hs he).2)
  have hw1 : A≤w:= (le_max_right ..).trans (le_max_left ..); have hw2:= mul_le_mul_of_nonneg_right (show z ≤ w from (le_max_left ..).trans (le_max_left ..)) he
  refine ⟨hm.tack le_rfl hw1 hw2,hk'.tack le_rfl hw1 hw2,?_⟩
  rw [psi_nurture _ hk i hn, psi_nurture _ hk j' hn]
  have ho : α≤min β δ:= min_le_right ..
  have hF:= (((crayon hβ hC H _ _ he U₁).2.tack (ho.trans (min_le_left ..)) le_rfl le_rfl).nativeCh S.L hQ).frame hk' hQ
  have hG:= hF.frame ((crayon hδ hB K _ _ he U₂).1.tack (ho.trans (min_le_right ..)) le_rfl le_rfl) hQ
  apply hG.tack le_rfl
  · exact (le_max_left ..).trans (le_max_right ..) -- defeq R?
  apply le_trans _ (mul_le_mul_of_nonneg_right (show X≤w from (le_max_right ..).trans (le_max_right ..)) he)
  exact le_of_eq (by unfold X g u v L f; ring)
end YM.RG08.Drift
