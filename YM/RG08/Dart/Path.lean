import YM.RG08.Dart.Plinth
/-! # Root analytics with actual sampled finite string. Covers term structure.
No requirement on translated oracle. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter Work.F02
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix Analysis Planned.PrimaryIntegral295
open scoped Topology BigOperators Real ContDiff Classical Matrix Matrix.Norms.Frobenius
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{r k i j:ℕ}{σ v C R:ℝ}{G:Gauge}{m:Side}
def Shot (G: Gauge)(R σ:ℝ): Prop:= ∀ r (b:Atom G r), VaultOn G (aTerm b) R (b.budget σ*priceSlot G^r)
lemma shot_ready (G:Gauge)(h:0<σ): ∃ R:ℝ,0<R ∧ Shot G R σ:= by
   obtain ⟨R,hR,H⟩:= term_vault G h; refine ⟨R,hR,fun r b m i=>?_⟩
   obtain ⟨v,hv,hV,hx⟩:=H r b _ i; exact ⟨v,hv, fun i hi=> (hV i hi).trans (mul_le_mul_of_nonneg_left ((le_abs_self (_^r)).trans_eq (abs_pow ..)) (by unfold Atom.budget Atom.magnitude; positivity)),hx⟩
-- allocate support fraction ℓ; Atom orientations chosen consistently $w$ recall price.Co wrapper.

def actionP (p: Beads (Loc G 2) r): Atom G r:= ⟨fun i=>walkSlot (plaqEquiv.symm (p i).2.1) (p i).1, Pi.single (fun i=> (p i).2.2) 1⟩
lemma budget_atom (p:Beads (Loc G 2) r): (actionP p).length=girth p+4*r:=by unfold Atom.length actionP; simp only [walkSlot_cost,sum_add_distrib,girth]; simp [mul_comm]
lemma mag_atom (p:Beads (Loc G 2) r): (actionP p).magnitude=1:= by unfold actionP Atom.magnitude; rw [sum_eq_single_of_mem (fun i=>(p i).2.2) (mem_univ _)]; simp; intro x hx he; simp [Pi.single_eq_of_ne he]
lemma bargain (k:ℕ) (G:Gauge) (hw:0<v)(hR:0<R) : ∃ C:ℝ,0≤C ∧ ∀ n:ℕ,(Fintype.card (Scope G k n):ℝ) ≤ C * Real.exp (R*(n:ℝ)) := by
   let F : ℝ:=16^k*(Fintype.card (Loc G 1):ℝ)^k
   refine ⟨F*(R⁻¹^(4*k)*(4*k).factorial*Real.exp R),by unfold F; positivity,fun i=>?_⟩
   have he: 0≤(i:ℝ):= Nat.cast_nonneg _
   have hx:= polynomial_cost hR he (4*k)
   have hp: (Fintype.card (Scope G k i):ℝ)= (2*(i:ℝ)+1)^(4*k)*(Fintype.card (Loc G 1):ℝ)^k:= by
       simp_rw [Scope,Fintype.card_fun,Fintype.card_fin]; rw [show Fintype.card (Lines G (village i) 1)=_ from Fintype.card_prod .., Lattice.site_card]; rw [show (village i).val=2*i+1 from rfl]; push_cast; rw [pow_mul, mul_pow]
   rw [hp, mul_comm _ ((Fintype.card (Loc G 1):ℝ)^k),mul_assoc F]; apply le_trans (b:= F*(1+(i:ℝ))^(4*k)) _ (mul_le_mul_of_nonneg_left hx (by unfold F; positivity)); unfold F
   have hh: 16^k * (1+(i:ℝ))^(4*k)=(2*(1+i:ℝ))^(4*k):=by rw [mul_pow,pow_mul 2]; norm_num
   rw [mul_comm (16^k),mul_assoc,hh]; gcongr; linarith

-- charge generation. allocate v~ (1/2 -~). $cost independent$.
lemma extraction (G: Gauge)(k j:ℕ)(hp:0<σ): ∃ v C:ℝ,0 < v ∧ v ≤ σ ∧ 0≤C ∧ ∀ i:Beads (Loc G 2) k, Quire.Lit (castleP (actionP i) j) v (C*ling σ i):= by
    let w:=σ/4; have he : 0<w:=by unfold w; positivity
    obtain ⟨R,hR,H⟩:= shot_ready G he; obtain ⟨A,hA,ha⟩:= bargain j G he he -- hR usage budget want w
    let K:=(priceSlot G^k*costNote j R); have hx:0≤K:=mul_nonneg (pow_nonneg (abs_nonneg _) _) (note_pos hR)
    let v:=w/(((j+1:ℕ):ℝ)*4); have hv:0<v:= by unfold v; positivity
    have hz:v ≤ σ:=by grw [show v≤w from div_le_self he.le (by push_cast; linarith [show 0≤ (j:ℝ) by positivity])]; unfold w; linarith
    refine ⟨v,A*K*Real.exp (σ*(4*k:ℕ)),hv,hz,by positivity,fun i=>?_⟩
    let b:=actionP i; refine Ink.raise (castle_price b j hv.le (H _ _) hR) ?_
    unfold homePrice Atom.budget; rw [mag_atom,one_mul,ling]
    let n:=b.length; let z:= Real.exp (v*(j*(4*n):ℕ)); let p:=Real.exp (w*n)
    have ht : z≤p:= Real.exp_monotone (by
        push_cast
        have hp:(j:ℝ)*4*v ≤w:=by
           apply le_trans (mul_le_mul_of_nonneg_right (show ((j:ℝ)*4)≤(↑(j+1:ℕ):ℝ)*4 by push_cast; linarith) hv.le); unfold v; rw [mul_div_cancel₀ _ (by positivity)]
        nlinarith only [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n : (0:ℝ)≤n)]) -- syntax
    calc (Fintype.card (Scope G j n):ℝ)*z*K*p ≤ (A*p)*p*K*p:= by gcongr; exact ha _
         _= A*K*Real.exp (w*n+w*n+w*n):= by simp only [Real.exp_add,p]; ring
         _ ≤ A*K*Real.exp (σ*↑(4*k))*Real.exp (σ*↑(girth i)):= by rw [mul_assoc (A*K),← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA hx); apply Real.exp_monotone; unfold n b; rw [budget_atom]; push_cast; unfold w; nlinarith only [hp, Nat.cast_nonneg (girth i) (α:=ℝ),Nat.cast_nonneg (α:=ℝ) k]
-- analytic bake as E-vector. canonical ident after absolute java at root frames. bare slots independent.
variable {F:Rooted E (Loc G 2) r}
abbrev curve (k:ℕ)(i : Beads (Loc G 2) r × Beads (Loc G 1) k):ℝ := castleP (actionP i.1) k i.2
def butter (F: Rooted E (Loc G 2) r)(k:ℕ) : Rooted E (Loc G 1) k:= sew (tub (sires F (curve k)) Prod.snd)
lemma curve_lit (G:Gauge)(k r:ℕ)(hp:0<σ): ∃ v C:ℝ,0<v ∧ v≤σ ∧ 0≤C ∧ ∀ U:Rooted E (Loc G 2) r,∀ B:ℝ, Quire.Lit U σ B → Quire.Ink (ling v ∘ Prod.snd) (sires U (curve k)) (C*B):= by
    obtain ⟨v,C,hv,hz,hC,H⟩:=extraction G r k hp; exact ⟨v,C,hv,hz,hC,fun U B h=>Ink.sires_cost h _ (curve k) hC H⟩
lemma curve_pens (h: Quire.Lit F σ C)(hv:0<σ)(k:ℕ): Pens (sires F (curve k)):=by
    obtain ⟨v,C,hv,_,_,ht⟩:= curve_lit (E:=E) G k r hv; exact (ht _ _ h).pens fun i=> ling_one hv.le _
lemma butter_h (h: Quire.Lit F σ C)(hv:0<σ)(k:ℕ) : Tidy (butter F k):= Tidy.sewn ((curve_pens h hv k).pours _)
-- cost before choices uses ALL ranks. may again purchase at fixed $E$; local.
lemma butter_cost (G:Gauge)(r k:ℕ)(hp:0<σ): ∃ v C:ℝ,0<v∧ v≤σ ∧ 0≤ C ∧ ∀ U:Rooted E (Loc G 2) r,∀ B, Quire.Lit U σ B → Quire.Lit (butter U k) v (C*B):= by
    obtain ⟨v,C,hv,hz,hC,H⟩:=curve_lit (E:=E) G k r hp; exact ⟨v,C,hv,hz,hC,fun U B h=> stitching ((H _ _ h).pour Prod.snd (ling_one hv.le))⟩
lemma butter_f (k:ℕ)(h:Quire.Lit F σ C)(he:0<σ)(P:E→L[ℝ] ℝ) : P ∘ butter F k=butter (P∘F) k:=by unfold butter; rw [sew_map,Pens.echo_pool _ (curve_pens h he _)]; congr 2; exact funext fun i=> map_smul ..
end YM.RG08.Dart
