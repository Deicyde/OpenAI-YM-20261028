import YM.FullVolume.Relay.Mint
/-
 Log and force rosters in Φ charts. Must earn the wing at every readable
 panel! The heads can't silently change over the tiny probes.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
set_option quotPrecheck false
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q d t c e t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 430000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q₀"=> A.B.a.budget (m+1)
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
open Board MergeProof Marker
variable {V I J:Type}[Fintype I][Fintype V][DecidableEq V]
open Luna Frets Empire Imago Luna.Aank Lotus
open FullVolume.Nectar Menu Accent Blush Extra.Histories Planned.GuardedAtom Guard
variable {B:Marker.Census V} (p:Booker A N m n T)(Z:sun→ Booker A N m n T)(o:V→ Site (A.B.a.S.side (m+1) n))
variable (M: Ship p Z o B I)(w:V→ℝ) (hw:∀ i,0<w i)
namespace Ship
-- specializations.
-- Estimator package for each `fire`. Use exact exponent.
variable (j:V)
structure OnlyP (j:V):Prop where
   targets : ∀ i, M.arm.mode i=B.fire j
variable (α:sun→ Config G (A.B.a.S.side (m+1) n)→ℂ)(ωs:sun→ Res G (A.B.a.S.side (m+1) n))(τ:sun→ℂ)
structure Token (j:V) (v:ℝ): Prop extends OnlyP p Z o M j where
   rollE (s:sun) x:M.allE p Z o s x=Poly.send (B.fire j) (α s x-τ s)
   rollK (s:sun) i x:M.allK p Z o s i x=Poly.send (B.fire j) (ωs s i x)
   counted : M.slot p Z o j ≤ v
include hw
lemma OnlyP.invoice (h:OnlyP p Z o M j): M.total p Z o w (Q₀).supportExponent = w j * M.slot p Z o j:=by
    unfold total slot; simp only [h.targets,↓reduceIte,BudgetPoint.mass,Poly.solo_toll]; rw [Finset.mul_sum]; exact sum_congr rfl (fun i _=>by ring)
omit hw
open Extra.Histories
-- natural packet extraction.
variable (k:Finset B.Mode)(hk:k⊆ lively B)
variable (E:sun→ Support (A.B.a.S.side (m+1) n)→ Config G (A.B.a.S.side (m+1) n)→ Poly B)(K:sun→ Box (A.B.a.S.side (m+1) n)→ Config G (A.B.a.S.side (m+1) n)→ Poly B)
-- combined portfolio purchases
include hw hk
lemma create (he:∀ s i,Burns o i (E s i) (A.B.a.budget (m+1)).threshold)(ht:∀ s i, Flow o i (K s i) (A.B.a.budget (m+1)).threshold) (hp:Pact w id E k (A.B.a.budget (m+1)).B e v) (h:Pact w Prod.fst K k (A.B.a.budget (m+1)).B e q):
   ∃ (I:Type) (ht:Fintype I) (M: Ship p Z o B I), M.total p Z o w e ≤2*v+2*q ∧ (∀ i,M.arm.mode i ∈ k) ∧ (∀ s u,M.allE p Z o s u=∑ i,proposed (E s i u) k)∧∀ s i u,M.allK p Z o s i u=proposed (K s i u) k:=by
   obtain ⟨I,hI,P₁,hP,hF,hΛ,hσ⟩:= hireLog p Z o w hw k hk E hp he
   obtain ⟨J,hJ,V₁,hV,hQ,hΨ,hφ⟩:= hireGas p Z o w hw k hk K h ht
   let P':= P₁.ballast p Z o V₁
   refine ⟨_, _,P',(P₁.paying p Z o V₁ w e).trans_le (add_le_add hP hV),P₁.remains p Z o V₁ k hF hQ,(fun s u=> by unfold P';rw [sphereE, hΛ, hΨ, add_zero]),fun s i u=> ?_⟩; unfold P'; rw [sphereK,hσ,hφ, zero_add]
lemma proposed_all (a:Poly B)(h:∀ i, a.part i≠0→ i∈ k): proposed a k=a:=by
   apply Eq.trans _ (Poly.studs a); apply sum_subset (subset_univ k); intro i _ hi;rw [of_not_not (mt (h i) hi),Poly.send_zero]
omit hk
lemma stars (he:∀ s, Carton o (E s) (K s) (A.B.a.budget (m+1)).threshold)(hp:Pact w id E (multiple B) (A.B.a.budget (m+1)).B e v) (h:Pact w Prod.fst K (multiple B) (A.B.a.budget (m+1)).B e q):∃ (I:Type) (ht:Fintype I) (M: Ship p Z o B I),
    M.total p Z o w e ≤ 2*v+2*q ∧ (∀ j:V, M.slot p Z o j=0)∧ (∀ s u, M.allE p Z o s u=∑ i,E s i u)∧(∀ s i u,M.allK p Z o s i u=K s i u) ∧ ∀ s j i u,M.oweK H p Z o s j i u=0:=by
    obtain ⟨I,hI,M,hM,hx,hP,hT⟩:=create p Z o w hw (multiple B) multiple_lively E K (fun s i=> (he s).exp i|>.1) (fun s i=> (he s).flag i|>.1) hp h
    have hh (j:V) (i:I): M.arm.mode i≠ B.fire j:=fun he=> by have H:=(FullVolume.Nectar.multiplicity _).1 (hx i);rw [he] at H; simp [Marker.Census.fire] at H
    refine ⟨I,hI,M,hM,fun j=> ?_,fun s u=> ?_,fun s i u=> ?_,fun s j i u=> ?_⟩
    · exact sum_eq_zero (fun i _=>if_neg (hh j i))
    · rw [hP]; apply sum_congr rfl; intro i _; exact proposed_all w hw (multiple B) multiple_lively _ (fun j h=> (FullVolume.Nectar.multiplicity _).2 ((he s|>.exp i).2 u j h))
    · rw [hT]; exact proposed_all w hw (multiple B) multiple_lively _ (fun j h=> (FullVolume.Nectar.multiplicity _).2 (((he s).flag i).2 u j h))
    exact sum_eq_zero (fun i' _=>if_neg (show (M.stamp p Z o s i').s≠ B.fire j from hh j i'))
omit hw
variable (u:sun→V→ℂ)
local notation "X0"=> fun s:sun=>(Z s).val.val.val
local notation "e0"=> (Q₀).supportExponent
private lemma sendSum {d: Finset I}(p:B.Mode)(f:I→ℂ): ∑ i∈ d,Poly.send p (f i)=Poly.send p (∑ i∈ d,f i):=by
    ext j; rw [Poly.part_sum]; simp_rw [Poly.part_send]; split; rfl; exact Finset.sum_const_zero ..
variable {Q C: V→ℝ}
lemma single (F:sun→ Config G (A.B.a.S.side (m+1) n)→Poly B)
     (h: Proceeds (fun i:sun=> (Z i).val.val.val) o w E K u ((A.B.a.budget (m+1))) F v q Q C): ∃ (I:Type) (z:Fintype I) (M: Ship p Z o B I), Token p Z o M (fun s=> singles E u s j) (fun s=> singlesK K s j) (fun s=> u s j) j (2*Q j+2*C j):=by
   let k: Finset B.Mode:={B.fire j}; let w₀:=fun _:V=> (1:ℝ)
   have hW :∀ i,0<w₀ i:= fun _=>zero_lt_one; have hk:k⊆ lively B:= singleton_subset_iff.mpr ((lively_ne _).2 (B.fire_hot j))
   have hp {I:Type}[Fintype I](r:I→Support (A.B.a.S.side (m+1) n)) (F : sun→I→ Config G (A.B.a.S.side (m+1) n)→ Poly B)(v:ℝ)(h:Treasure (fun i=> Real.exp (e0 * coverNumber (A.B.a.budget (m+1)).B (r i))) (fun s i x=> (F s i x).part (B.fire j)) v): Pact w₀ r F k (A.B.a.budget (m+1)).B e0 v:=by
        obtain ⟨b,hb,h⟩:=h.coins
        have he i:(i:↑k).val= B.fire j:=Finset.mem_singleton.mp i.property
        refine ⟨b ∘ Prod.fst,?_,fun i=>?_⟩
        · rw [Fintype.sum_prod_type]; simp_rw [he,Poly.solo_toll,Function.comp_apply]; unfold w₀ k; simp only [mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_coe,Finset.card_singleton,one_smul]; exact hb
        simp_rw [he]; exact h _
   obtain ⟨I,hI,M,hM,hP,hG,hm⟩:= create p Z o w₀ hW k hk E K (h.realP.permitE) (h.realP.permitK) (hp id E (Q j) (h.singleE j)) (hp Prod.fst K (C j) (h.singleK j))
   have hh: OnlyP p Z o M j:= ⟨fun i=> mem_singleton.mp (hP i)⟩
   refine ⟨I,hI,M,{ hh with
                    rollE:=fun s x=> ?_
                    rollK:=fun s i x=>?_
                    counted:=?_ }⟩
   · rw [hG]; unfold proposed k singles; simp_rw [sum_singleton]; change _= Poly.send _ _; simp only [add_sub_cancel_left]; exact sendSum ..
   · rw [hm]; unfold proposed k; rw [sum_singleton]
   rw [OnlyP.invoice p Z o M w₀ hW j hh] at hM; simpa only [w₀,one_mul] using! hM
end Ship
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Ship.stars
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Ship.single
