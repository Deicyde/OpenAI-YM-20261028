import YM.RG08.Rudder.Loop.Coins
import YM.RG08.Rudder.FinalLegs

/-! Rank TWO lift for translation-invariant cells with first moment zero.
Eliminates the obstruction of the positional arbitrary arity proof in this case directly
(bypasses Laurent divisibility). This supplements rather than replaces BoxChain.multi n≥3.
-/
noncomputable section
namespace YM.RG08.Rudder.Loop
open scoped Topology BigOperators Classical
open Forms Packets Finset Function Lattice Laurent Pert.Bulk Exterior AnalyticNext.QuarticMatch.BoxChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "o"=> (0:Fin 2)
local notation "p"=> (Fin.succ (0:Fin 1))

lemma Shade.empty {A:ProductR}(h:Shade A)(ha:Cohere A):EmptySum A o:=by
 intro X
 simp_rw [peek,edit_o,prices ha]
 let H:Equiv.Perm Cover:=(Equiv.neg _).trans (Equiv.addRight (X p).1)
 have he(v:Cover):H v=(X p).1-v:=by change -v+(X p).1=_;abel
 change (∑' x:Cover, col A ∅ (X p).2 ((X p).1-x))=0
 rw [tsum_congr (f:=fun x=> _) (g:=fun x=>col A ∅ (X p).2 (H x)) (fun x=>by rw [he]),H.tsum_eq]
 exact h .. -- ? field ellipsis

lemma Shade.static {A:ProductR}{σ C:ℝ}(hp:Pricing A σ C)(h:Shade A):Static (lower o A):=by
 intro i j a;rw [obverse hp,h];simp

theorem double (σ:ℝ)(he:0<σ):∃ θ K:ℝ,0<θ∧θ≤σ∧0≤K∧∀ (C:ℝ)(T:ProductR), Pricing T σ C→(∀ i,Rank T i 1∧ClosedSlot T i)→Static T→
 ∃ U:ProductR,Pricing U θ (K*C)∧T=YM.AnalyticNext.QuarticMatch.BoxChain.solve (List.finRange 2) U∧ ∀ i,Rank U i 2:=by
 have hi:p≠o:=Fin.succ_ne_zero _
 obtain ⟨a,M,ha,hA,hM,H⟩:= arm (V:=ℝ) p o hi.symm σ he 1
 let B:= debit a * M -- ambiguous
 have hB:0≤B:=mul_nonneg (debit_pos _) hM
 obtain ⟨b,D,hb,hb',hD,H₂⟩:=arm (V:=ℝ) p o hi.symm a ha 2
 let C₁:=D*B;have h1:0≤ C₁:=mul_nonneg hD hB
 obtain ⟨v,P,hv,hv',hP,H₃⟩:=arm (V:=ℝ) o p hi b hb 0
 let C₂:= M+ (debit v*P)*C₁; have h2:0≤ C₂:=add_nonneg hM (mul_nonneg (mul_nonneg (debit_pos _) hP) h1)
 obtain ⟨θ,Q,hθ,hθ',hQ,H₄⟩:=arm (V:=ℝ) o p hi v hv 1
 refine ⟨θ,Q*C₂,hθ,hθ'.trans (hv'.trans (hb'.trans hA)),mul_nonneg hQ h2,?_⟩
 intro C T hT hk hs
 obtain ⟨F,hF,hf,hp,hI,-⟩:=H C T hT (hk p).1 (hk p).2 (by omega)
 let G:=lower o F
 have hG:Pricing G a (B*C):=by unfold B;rw [mul_assoc];exact hF.smaller o
 have hg:Rank G p 2:=hf.keeps hi
 have ho:Rank F o 1:=hI o hi.symm _ (hk o).1
 have hz:ClosedSlot G p:=by
    unfold ClosedSlot G;rw [lower_switch,hp];exact (hk o).2
 obtain ⟨Y,hY,hm,hN,hQ',-⟩:=H₂ _ G hG hg hz (by omega)
 have h3:Pricing Y b (C₁*C):=by unfold C₁;rw [mul_assoc];exact hY
 -- direct emptiness via successive moments on v
 have hc:Shade F:=ninety hF (r:=2) (by omega) hf (hp ▸ hs)
 have hy:Shade Y:=ninety hY (r:=3) (by omega) hm (hN ▸ hc.static hF)
 have h0:Rank Y o 0:=hQ' o hi.symm 0 ho.descent
 have hj:ClosedSlot Y o:=by
    funext X;rw [lower_at];apply sum_eq_zero;intro i _;rw [sect_at];split
    · rfl
    have he (x:Cover):peek o X Y (x,insert i (X o).2)=0:=h0 _ (by simp)
    rw [he,he,sub_self,smul_zero]
 obtain ⟨Z,hZ,hh,hD',hL,-⟩:= H₃ _ Y h3 h0 hj (fun _=>hy.empty h3.same)
 let X:=F-lower p Z
 have HX:Pricing X v (C₂*C):=by unfold C₂; rw [add_mul,mul_assoc (debit v),mul_assoc,mul_assoc]; exact (hF.widen hv (hv'.trans hb') le_rfl).sub (hZ.smaller p)
 have Hx:Rank X p 2:= hf.sub ((hL p hi 3 hm).descent)
 have Hw:Rank X o 1:=ho.sub (hh.keeps hi.symm)
 have HT:lower p X=T:=by unfold X;rw [map_sub,lower_twice,sub_zero,hp]
 have HD:ClosedSlot X o:=by unfold X ClosedSlot;rw [map_sub,lower_switch,hD',hN];exact sub_self _
 obtain ⟨U,hU,hu,hR,hℓ,-⟩:=H₄ _ X HX Hw HD (by omega)
 refine ⟨U,by rw [mul_assoc];exact hU,?_,?_⟩
 · have he: List.finRange 2=[o,p]:=rfl
   rw [he,solve_head,solve_head,solve_empty,lower_switch,hR,HT]
 intro k; cases k using Fin.cases with
 | zero=>exact hu
 | succ k=>rw [Subsingleton.elim k (0:Fin 1)];exact hℓ p hi _ Hx

/-- Rank TWO simultaneous linear lift of position kernels. `Static` may be provided
by explicit Taylor operations or by Ward plus coordinate reversal hypotheses separately.
 Conclusion does not yet retain affine-null zero mode on the lifted U (needs kinetic split).
-/
def noPole {I:Type}(A:Raw I 2):Prop:=∀ y,Static (hum A y)

theorem doubleLift (I:Type)[Fintype I](σ:ℝ)(hs:0<σ):∃ α Q:ℝ,0<α∧α≤σ∧0≤Q∧
   ∀ (F:Raw I 2) (C:ℝ),0≤C→ Cohort F→Graded F 1→Closing F→noPole F→Held (carpet (Tone I)) σ C F→
      let U:= lineLift I 1 α F
      picture I 2 U=F ∧ Cohort U ∧ Graded U 2 ∧ Held (carpet (Tone I)) (α/2) (Q*C) U ∧
   ∀ (A:Raw I 2)(t:ℝ),0≤t→ Cohort A→Graded A 1→Closing A→noPole A→Held (carpet (Tone I)) σ t A→
      lineLift I 1 α (F-A)=U - lineLift I 1 α A:=by
 obtain ⟨θ,K,he,hk,hφ,H₀⟩:=double σ hs
 let α:=θ/2; let a:=Tone I; let L:=(picture I 2).comp (truth I 2 2)
 let fee:=debit' a 2 θ; have hf:0≤fee:=debit'_nn he (by omega)
 have hx:0<α:=by unfold α;linarith
 have hp (F:Raw I 2)(C:ℝ)(hP:0≤C)(hc:Cohort F)(hr:Graded F 1)(hC:Closing F)(hz:noPole F)(ht:Held (carpet (Tone I)) σ C F):Possible o (I:=a) α L (fee*(K*C)) F:=by
    choose f hN hv hF using (fun y=>H₀ C (hum F y) (NextTo.unit hs hP hc ht (by omega) y) (fun i=>⟨hr y i,hC y i⟩) (hz y))
    have hu: Graded (joinC f) (fun _=>2):=fun y i=>hF y i
    have he':NextTo (joinC f) θ (K*C):=hN
    refine ⟨hx,mul_nonneg hf (mul_nonneg hφ hP),joinC f,?_,he'.cohort,he'.held (by omega) (mul_nonneg hφ hP) he⟩
    change picture _ _ (truth _ _ _ (joinC f))=F
    rw [intact _ hu,←hum_back (picture I 2 (joinC f)),←hum_back F];congr 1
    funext y;rw [picture,patch_eval,hv y];rfl
 let v:=debit' a 2 α; have hv:0≤v:=debit'_nn hx (by omega)
 use α,(v*(2*Fintype.card a))*(fee*K)
 refine ⟨hx,by unfold α;linarith,by positivity,?_⟩
 intro F C hP hc hr hC hS ht U
 have hh:=hp _ _ hP hc hr hC hS ht
 obtain ⟨hEq,hco,hH⟩:=pays hh
 refine ⟨hEq,true_cohort hco _,rank_truth 2 _,(true_held _ hH).mono le_rfl (by unfold v;rw [mul_assoc _ _ C,mul_assoc fee K C]) (fun _=>le_rfl),?_⟩
 intro A t hA ho hw hz hL hY; change truth I _ _ (answer o α L (F-A))=_
 rw [stable hh (hp A t hA ho hw hz hL hY),map_sub];rfl
end YM.RG08.Rudder.Loop
