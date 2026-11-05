import YM.FullVolume.Relay.Quiet
import YM.MergeProof.Close
import YM.MergeProof.Wicket
import YM.MergeProof.Bungalow
/-!
 The **Attic**: weighted analytic budget on multisource (hot) arrays. Exempts
 singleton data, which is formatted, compressed and charged separately. The
 estimate is ON the same particular packets, not merely an existential at
 each s. Work on the real diameter for the algebraic constraints (mask,
 alias, alignment and exact expression).
 The aperture can be preserved over the recursion.

 `attic_close` buys restoration at a possibly changed radius by an explicit
 weighted repeg. Needs the φ controlling K substitution exactly; crucial for
 the singleton slots to refresh from the current calibration.

 All statements here unit local; no program assumptions on Γ. Receipts will
 produce the actual Bounds below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson Ac
variable {V I:Type} [DecidableEq V] [Fintype V] {B:Marker.Census V}{G:Gauge}{n:Side}
variable {p:BudgetPoint} (F:sun→ Rep G n)(o:V→Site n)(w w':V→ℝ)(hw:∀ i,0<w i)
structure Attic (B:Marker.Census V)(F:sun→Rep G n)(p:BudgetPoint)(o:V→ Site n)(w:V→ℝ)
   (f:sun→ Config G n→Poly B) (α:sun→ V→ Config G n→ℂ)(ωs:sun→ V→ Box n→ Config G n→ℂ)(t q:ℝ):Prop where
   board : ∃ E K, (∀ s:sun,Carton o (E s) (K s) p.threshold ∧ f s=restore (F s) (α s) (ωs s) (E s) (K s))∧ Pact w id E (multiple B) p.B t q ∧ Pact w Prod.fst K (multiple B) p.B t q
variable {f:sun→ Config G n→Poly B} {α:sun→ V→ Config G n→ℂ}{ωs:sun→ V→ Box n→ Config G n→ℂ}
variable (hP:∀ s,(F s).p=p)
variable {z u v W σ a c e T s t q:ℝ}
-- oven-style real witnesses before closure.
variable (E:sun→ Support n→ Config G n→ Poly B)(K:sun→ Box n→ Config G n→Poly B)
-- use Namespace const for affordability.
structure Refresh (X : sun→ Config G n→ Poly B):Prop where
   permitE s: ∀ i,Burns o i (E s i) p.threshold
   permitK s: ∀ i,Flow o i (K s i) p.threshold
   quietE s U : (X s U).part B.quiet=0
   echoK s i U: (K s i U).part B.quiet=profile (F s).activities (fun j=> Complex.ofReal ∘ (F s).activities.K j) i U
   highE s U (j:B.Mode):2 ≤ j.val.card→(X s U).part j=(∑ i,E s i U).part j
variable {X:sun→ Config G n→ Poly B}(hE:Refresh F o E K X (p:=p))
   (θ:sun→ V→ Response G n)(hθ:∀ s i,∃ t, MergeProof.Attainment p (o i) (θ s i) t)
   (hj:∀ s j i U,(K s i U).part (B.fire j)+ hook (F s|>.activities) p.threshold (θ s j) i U=ωs s j i U)
abbrev visaK (F:sun→ Rep G n) (s:sun):=  profile (F s).activities (fun j=> Complex.ofReal ∘ (F s).activities.K j)
variable (h:∀ s,f s=play (F s) B (K s) (X s))
open PhysicalNext.Repeat
include hw hP h hE hθ hj
set_option maxHeartbeats 430000 in
lemma attic_close (P:V→ℝ)(hω:∀ i,Treasure (fun j:Support n=>Real.exp (p.supportExponent*coverNumber p.B j)) (fun t=> θ t i) (P i))(hK:WindowP (visaK F) Prod.fst p.B p.supportExponent W)
    (hmK: Pact w Prod.fst K (lively B) p.B p.supportExponent u)(hmE:Pact w id E (multiple B) p.B p.supportExponent s) (hp: ∀ x:sun,(F x).activities.Valid p T z)
    (hΦ:∀ x (i:V),∃ k:ℕ→ Config G n→ℂ, Dominated k ∧ ωs x i=profile (F x).activities k ∧ ∀ U,(f x U).part (B.fire i)= Accent.coin (F x) (α x i) k U)
    (hit:∀ x U,(F x).eval U≠0)
    (hk: p.supportExponent-1=t+e) (hc:0≤p.supportExponent-1)(ht:∑ i,w i*P i ≤ v)
    (hV:(((p.B+p.B+1:ℕ):ℝ))^4*((W+u)+v) ≤ 1)(hd:0 ≤ c)
    (hB:Repegs o p.B w w' e c B)(hs:c*s ≤ q)(ha:c*(Fintype.card V * (Real.exp ((W+u)+v)-1)) ≤ q) : Attic B F p o w' f α ωs t q:=by
   let K'(i:sun):= Accent.closure (K i) (conviction (θ i) B) Prod.snd p.threshold
   let Z(i:sun):= X i-kelp (θ i) B
   have hx x: ∃ t, Garnish p o (θ x) w p.supportExponent t:=by
       choose t hT using hθ x
       refine ⟨∑ i,|w i*t i|, cloth hT (fun i=> ?_) (fun i=> (hw i).le)⟩
       exact (le_abs_self _).trans (single_le_sum (fun i _=>abs_nonneg (w i*t i)) (mem_univ i))
   choose A hA using hx
   have hcW (x:sun) : f x=play (F x) B (K' x) (Z x):=by
       rw [h]; unfold K' Z; rw [← hP x]; exact funext (fun U=> reversal (F x) (θ x) (K x) (X x) ((hP x).symm ▸ hA x) ((hP x).symm ▸ hE.permitK x) U (hE.quietE x U))
   have hy (s):= threshed (K s) (conviction (θ s) B) Prod.snd p.threshold (hE.permitK s) (dresses _ _ (hA s))
   have hPq : Polaris w Prod.fst K p.B p.supportExponent (W+u):=by
       apply Polaris.from_modes hw hmK; rw [show receive K B.quiet=visaK F from funext fun i=>funext fun j=>funext (hE.echoK i j)]; exact hK
   have hZ : Polaris w Prod.snd (fun i:sun=>conviction (θ i) B) p.B p.supportExponent v:=by
       obtain ⟨f,hf,h,h0⟩:=conviction_paid (B:=B) hw θ P hω
       exact ⟨f,hf,(fun i=> budget_loosen (h i) ht),h0⟩
   have he : p.supportExponent=p.supportExponent-1+1:=by ring
   have hψ := Polaris.glimmers hw K (fun i=>conviction (θ i) B) Prod.snd p.threshold (he ▸ hPq) (he ▸ hZ) hc hV -- `w` etc
   have hgk : Pact w Prod.fst K' (multiple B) p.B (t+e) (↑(Fintype.card V)*(Real.exp ((W+u)+v)-1)):= hk ▸ Polaris.roll_up hw hψ (fun s i=> (hy s i).toBorne) multiple_lively
   have hge : Pact w id E (multiple B) p.B (t+e) s:= hmE.lower hw (le_trans hk.symm.le (by linarith))
   have hpp : ∀ x, Carton o (G1 E x) (G1 K' x) p.threshold ∧ f x=restore (F x) (α x) (ωs x) (G1 E x) (G1 K' x):=by
       intro x; let Y:= F x; choose k hQ kw h0 using hΦ x
       let S' i:= profile Y.activities (k i)
       have hv:(ωs x)=S':=funext kw
       have hg : Y.activities.Valid Y.p T z:=(hP x).symm ▸ hp x
       have hW(i U): (K' x i U).part B.quiet=profile Y.activities (fun j=> Complex.ofReal ∘ Y.activities.K j) i U:=(wine (K x) (conviction (θ x) B) Prod.snd p.threshold _ i (fun i=> hE.permitK x i |>.permits U) (corn_quiet (θ x) B U)).trans (hE.echoK x i U)
       have hU(i U j): (K' x j U).part (B.fire i)=S' i j U:=by
          unfold K'; rw [←hP x]; refine (posts (F x) (θ x) (K x) ((hP x).symm ▸ (hE.permitK x)) (hE.echoK x) hg U i j).trans ?_; rw [hP x,hj, kw] -- `ωs` hv
       rw [← show Y.p=p from hP x, show F x=Y from rfl, show f x=_ from hcW x,hv]; apply plank Y B (K' x) (Z x) (α x) k hg hW ?_ ((hP x).symm ▸ hE.permitE x) ((hP x).symm ▸ hy x) hQ hU (fun i U=> hcW x ▸ h0 i U) (hit x)
       · intro U j hj; unfold Z; simp only [Pi.sub_apply,Extra.Trajectories.part_sub,kelp,corn_light _ j hj U,sub_zero,hE.highE x U j hj]
       intro U; unfold Z; simp only [Pi.sub_apply,Extra.Trajectories.part_sub,kelp,Poly.part_sum,hE.quietE x U,corn_quiet _ _ _,sum_const_zero,sub_zero]
   exact ⟨G1 E, G1 K',hpp,(Pact.alter hw (hge.eighth_part fun _ h=>h) (fun x i=>(hpp x).1.exp i|>.1.toBorne) (subset_refl _) hB hd).grows hs,(Pact.alter hw (hgk.eighth_part fun _ h=>h) (fun x i=>(hpp x).1.flag i|>.1.toBorne) (subset_refl _) hB hd).grows ha⟩
-- argument order check no `omit hw` as inside include.
omit hP h θ hθ hj hE
lemma attic_shrink (h:Attic B F p o w f α ωs t q) (hC:Repegs o p.B w w' 0 1 B): Attic B F p o w' f α ωs t q:=by
   obtain ⟨E,K,hE,hF,hK⟩:=h.board
   refine ⟨E,K,hE, (Pact.alter hw (add_zero t|>.symm ▸ hF) (fun s i=>(hE s).1.exp i|>.1.toBorne) (subset_refl _) hC zero_le_one).grows ?_,(Pact.alter hw (add_zero t|>.symm ▸ hK) (fun s i=>(hE s).1.flag i|>.1.toBorne) (subset_refl _) hC zero_le_one).grows ?_⟩<;> rw [one_mul]
end YM.FullVolume.Nectar
#print axioms YM.FullVolume.Nectar.attic_close
#print axioms YM.FullVolume.Nectar.attic_shrink
