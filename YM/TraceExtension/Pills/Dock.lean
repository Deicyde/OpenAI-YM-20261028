import YM.TraceExtension.Pills.Joy
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} {P:Support n}{Q Q': Peat G n}{Y: Gal G n} {k:ℕ}{σ A C R D D' L:ℝ}
lemma Heath (h:HearthV Q P k A D)(hp:HearthV Q' P k C D): HearthV (Q+Q') P k (A+C) D:=⟨(loom _ _).add_mem h.silk hp.silk,fun U V hv=> congr_arg₂ (·+·) (h.pillar _ _ hv) (hp.pillar _ _ hv),fun _ _=> congr_arg₂ (·+·) (h.symU ..) (hp.symU ..),fun X _ _ W x ha=> (h.choir X W x ha).add (hp.choir X W x ha),fun X _ _ W y hv=> (h.price X W y hv).add (hp.price X W y hv)⟩
lemma HearthV.plusR {V:Support n}(h:HearthV Q P k A D)(hp:P⊆ V):HearthV Q V k A D:= ⟨h.silk,fun U W ht=> h.pillar _ _ (agrees_mono ht hp),h.symU,h.choir,h.price⟩
def DockAmt(G:Gauge)(B:ℕ)(T:ℝ)(s u:ℕ)(C a:ℝ):ℝ:= ( (s+s+1:ℕ)^4 :ℕ)* (bankCost B*(T * (momentPrice u (a/2)*C)))
def pier(s:ℕ)(A E:ℝ):ℝ:= A*E*((10+s+(10+s)+1)^ (4:ℕ))
lemma sandy (hG:G.Simple)(k:ℕ)(A:ℝ)(ha:0 ≤ A):∃ D T:ℝ, ∃ u:ℕ,1≤ D ∧ 0 ≤T ∧ ∀ (n:Side) (R:Rep G n)(L:Finset ℕ)(σ B C:ℝ), R.path.Bounds R.clip σ B C → 2 ≤ R.p.B → ∀ (Y:Axis→Gal G n)(c:Axis→ℝ)(r l:ℕ), 10≤ r→ (∀ i, Clouded (Y i) (sprout 0 l))→ (∀ i,Climate (Y i) k (c i) A)→
    let F:= R.path.loop; let S:= ski R loopF L r; let Q:= spikes R loopF L r; let Z:= ink Q F; let W:= sprout (0:Site n) (salo R l r); let T1:= paper (swat Q) (shade Q F) (n:=n); let U:= paper univ Z (n:=n); let p:= DockAmt G R.p.B D l u C σ;
    ∀ t:ℝ,(∑ i:Colour,(Z i).magnitude) ≤ t→ let f:= pier l t T; (∀ i, rill S (Y i) = rill T1 (Y i)-rill U (Y i)) ∧
    (∀ i,HearthV (rill U (Y i)) W k (blare G W k (c i) f) A) ∧ (∀ i,HearthV (rill S (Y i)) W k (blare G W k (c i) p) A) ∧
    (∀ a:G.ColorIndex,Nonwrapping W 0 →2*(salo R l r+1+1+r)+6 < n.val→ Loft.Holt a (fun i=> rill T1 (Y i) ∘ input G n)=0):=by
    obtain ⟨Q,hQ,hq⟩:= phare G hG A ha k
    obtain ⟨D,u,hD,H⟩:= policy G (k+1) Q hQ; obtain ⟨T,hT,Gt⟩:= paid_h G Q hQ (k+1) 10
    refine ⟨D,T,u,hD,hT,fun n R L σ B C h hB Y c r l hl hv ht=>?_⟩; intro F S Q' Z W P U p t hx f
    let Hm:= sprout (0:Site n) l; have hP(i):Clouded (Y i) W:= (hv i).wider (sprout_mono _ (show l ≤ salo R l r from by unfold salo; omega))
    have hZ(i): (Z i).Invariant:= pristine _ _ (fun i _=>(h.invariant i).1) i
    have hz(i): HearthV (rill U (Y i)) W k (blare G W k (c i) f) A:=by
        let T':= prunedX (0:Site n) l 10 Z univ
        have hV: Splendor T' W (k+1) f Q:=by
           have hF:= Gt Colour n Z univ hG (fun i _=>hZ _) (fun i _=> ink_length ..) t hx l 0
           refine hF.up (sprout_mono 0 (show 10+(10+l) ≤ _ from ?_)) (le_of_eq ?_)
           · unfold salo; omega
           unfold f pier;push_cast; ring
        rw [show rill U (Y i)=rill T' (Y i) from (halo_eq Z univ (hv i) (t:=10) (fun i _=>ink_length ..)).symm]; exact hq _ (Y i) T' W (c i) f (drip Z univ) (ht _) (hP i) hV
    have hw(i): HearthV (rill S (Y i)) W k (blare G W k (c i) p) A:=by
        rw [show rill S (Y i)=rill (prun R loopF Hm Q') (Y i) from husk R loopF Q' (hv i) hB]; exact hq _ _ _ _ _ _ (hymn R loopF Q' Hm) (ht _) (hP i) (H ℕ loopF _ _ _ _ _ _ _ h hG hB (offloop R h) L l r)
    have he: P=S+U:=by
        unfold S ski; rw [fromR R]; unfold P U; ext1 x; simp only [Pi.add_apply,paper,swat,sum_disjSum,mul_add];rfl
    have hp(i): rill P (Y i)=rill S (Y i)+rill U (Y i):=by
        rw[he]; refine bankers S U ?_ (stood_w univ Z); rw[show S=_ from fromR R Q']; exact stood_w _ _
    refine ⟨fun i=> (by rw[hp]; abel),hz,hw,fun a hy hm=>?_⟩
    refine blank_h (swat Q') (shade Q' F) (Q:=fun _ _=>0) (fun i hi=>?_) (valid Q' F) hP hG hy (Finset.Subset.refl _) hm (fun i hi=> ?_) a (fun i=> by
       change LocalOn W (rill P (Y i)); rw[hp]; exact ((Heath (hw i) (hz i)).pillar))
    · cases i with
      | inl i=> exact (h.invariant i).1
      | inr i=>exact hZ i
    cases i with
    | inl i=>exact (mem_filter.mp (inl_mem_disjSum.mp hi)).2
    | inr i=>exact le_trans (ink_length Q' F i) hl
end YM.Trace.Pills
#print axioms YM.Trace.Pills.sandy
