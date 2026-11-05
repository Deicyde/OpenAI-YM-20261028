import YM.TraceExtension.Pi.Slide
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft
open Source Source.Drops Labels Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {d n k:ℕ}{G:Gauge}{s:Side}{F: Peat G s}{v:Label G d}
variable {H:Hol G}{o:Site s}
lemma chafe (h: JetTest H o v (Complex.ofRealCLM ∘ F))(J: Jet G)(hk:k≤d):
    Labels.read J (tier k v.val)=leading k (fun t:ℝ=> (F (pulseC o H d (engineered t (trunk d J))):ℂ)):=by
    have he:(fun t:ℝ=> (F (pulseC o H d (engineered t (trunk d J))):ℂ))=(Complex.ofRealCLM ∘ F)∘ H.testLinks d o J:=by
       funext i; rw[Function.comp_apply,test_scaled];rfl
    rw[he,leading,(show iteratedDeriv k ((Complex.ofRealCLM ∘ F) ∘ H.testLinks d o J) 0=_ from (h J).2.2 k hk),deriv_read, inv_smul_smul₀ (by positivity)]
abbrev sheen (F:Peat G s)(x y:Link G s):ℝ:=iteratedFDeriv ℝ 2 (F ∘ input G s) 0 ![x,y]
def ivy (o: Site s)(X:Taylor G n): Link G s:= stepC o (variation X)
lemma shot_t {k:ℕ}(h:Cleric F)(hp:G.Simple)(he:JetTest H o v (Complex.ofRealCLM ∘ F))(hd:2 ≤ d)(J: Jet G)(hk:k≤d)(hv:k<4): Labels.read J (tier k v.val)=if k=0 then ↑(F 1) else 0:=by
   rw[chafe he J hk]; obtain ⟨hs,hf,ht⟩:=artist H o hd h hp; let A:= fun x:Snap G d=> (F (pulseC o H d x):ℂ); change leading k (fun t=> A (engineered t _))=_; rw[snap_tiny (F:=A) (hs.of_le le_top) hf J hd hk hv,show A 0=(F 1:ℂ) by unfold A;rw[pulseC_zero]]
lemma stamp4 (h:Cleric F)(hp:G.Simple)(he:JetTest H o v (Complex.ofRealCLM∘ F))(hd:4 ≤ d)(J:Jet G):
    Labels.read J (tier 4 v.val)=(↑((1/2:ℝ)* sheen F (ivy o (J 0)) (ivy o (J 0))):ℂ):=by
    rw[chafe he J hd]; obtain ⟨hs,hf,ht⟩:= artist H o (show 2 ≤ d by omega) h hp; let i:Fin (d-1):=⟨0,by omega⟩; let A:= Complex.ofRealCLM ∘ F ∘ pulseC o H d
    have hz: leading 4 (fun t=> A (engineered t (trunk d J)))=(1/2:ℝ) • (↑(sheen F (ivy o (J 0)) (ivy o (J 0))):ℂ):=by rw[snap_p4 (F:=A) (hs.of_le le_top) hf J hd]; exact congr_arg _ (ht i i (J 0) (J 0))
    exact Eq.trans hz (Complex.ofReal_mul ..).symm
lemma stamp5 (h:Cleric F)(hp:G.Simple)(he:JetTest H o v (Complex.ofRealCLM∘ F))(hd:5≤d)(J:Jet G):
    Labels.read J (tier 5 v.val)=(↑(sheen F (ivy o (J 0)) (ivy o (J 1))):ℂ):=by
    rw [chafe he J hd]; obtain ⟨hs,hf,Hx⟩:= artist H o (show 2 ≤ d by omega) h hp
    exact Eq.trans (snap_p5 (hs.of_le le_top) hf J hd) (Hx ⟨0,by omega⟩ ⟨1,by omega⟩ (J 0) (J 1))
lemma vista4 {v:Label G 4} (h:Cleric F)(hp:G.Simple)(he:JetTest H o v (Complex.ofRealCLM∘ F))(J:Jet G):
    Labels.read J v.val=(↑(F 1+1/2*sheen F (ivy o (J 0)) (ivy o (J 0))):ℂ):=by
    conv_lhs=> rw[← limited_cap 4 _ v.property.1,capRead,map_sum];
    simp only [sum_range_succ,sum_range_zero,zero_add]; rw [stamp4 h hp he (by decide) J, shot_t (k:=3) h hp he (by decide) J (by decide) (by decide), shot_t (k:=2) h hp he (by decide) J (by decide) (by decide),shot_t (k:=1) h hp he (by decide) J (by decide) (by decide), shot_t (k:=0) h hp he (by decide) J (by decide) (by decide)]; norm_num
lemma vista5 {v:Label G 5} (h:Cleric F)(hp:G.Simple)(he:JetTest H o v (Complex.ofRealCLM∘ F))(J:Jet G):
    Labels.read J v.val=(↑(F 1+1/2*sheen F (ivy o (J 0)) (ivy o (J 0))+sheen F (ivy o (J 0)) (ivy o (J 1))):ℂ):=by
    conv_lhs=> rw[← limited_cap 5 _ v.property.1,capRead,map_sum];
    simp only [sum_range_succ,sum_range_zero,zero_add]; rw [stamp4 h hp he (by decide) J,stamp5 h hp he (by decide) J, shot_t (k:=3) h hp he (by decide) J (by decide) (by decide), shot_t (k:=2) h hp he (by decide) J (by decide) (by decide),shot_t (k:=1) h hp he (by decide) J (by decide) (by decide), shot_t (k:=0) h hp he (by decide) J (by decide) (by decide)]; norm_num
end YM.Trace.Kits
