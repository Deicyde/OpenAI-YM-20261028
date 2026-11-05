import YM.RG08.Forms.Weld

/-!
# Difference widths and bills at unchanged rank after heat contractions
-/
noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I : Type}{p q n : ℕ} {Γ Γ' : Line I}{F F' : Flake (p+1) I}{G G' : Flake (q+1) I} {d : Ground I}{σ C C' D D' B B':ℝ}

theorem bridge_compare (hn:0<p+q) (h : Held d σ C F)(hF : Held d σ C' F') (hG: Held d σ D G)(hg: Held d σ D' G') (hk: Wire d σ B Γ)(hk':Wire d σ B' Γ')(hnC:0≤C)(hnF:0≤C')(hnG:0≤D)(hn':0≤D'):
 bridge Γ F G - bridge Γ' F' G' = bridge Γ (F-F') G + bridge (Γ-Γ') F' G + bridge Γ' F' (G-G') := by
 unfold bridge; rw [← bleach_sub, ← bleach_add,← bleach_add]
 congr 1; ext x
 have h0:=(binary_sum h hG hk hnC hnG hn x).of_norm
 have h1:=(binary_sum hF hG hk hnF hnG hn x).of_norm
 have h2:=(binary_sum hF hG hk' hnF hnG hn x).of_norm
 have h3:=(binary_sum hF hg hk' hnF hn' hn x).of_norm
 have he1 (i):seam Γ (F-F') G x i=seam Γ F G x i - seam Γ F' G x i:=by simp [seam,sub_mul]
 have he2 (i):seam (Γ-Γ') F' G x i=seam Γ F' G x i - seam Γ' F' G x i:=by simp [seam,mul_sub,sub_mul]
 have he3 (i):seam Γ' F' (G-G') x i=seam Γ' F' G x i - seam Γ' F' G' x i:=by simp [seam,mul_sub]
 simp only [Pi.sub_apply,Pi.add_apply,weld,he1,he2,he3,h0.tsum_sub h1,h1.tsum_sub h2,h2.tsum_sub h3];ring

theorem Held.lap_diff (hm:0<n){F F':Flake (n+2) I}{r t:ℝ} (h:Held d σ C F)(h':Held d σ C' F') (hk:Wire d σ B Γ)(hk':Wire d σ B' Γ')(hΔ: Held d σ r (F-F'))(hΓ:Wire d σ t (Γ-Γ'))(hr:0≤r)(hC':0≤C'):
 Held d σ (r*B + C'*t) (Forms.lap Γ F - Forms.lap Γ' F'):=by
 rw [lap_compare hm h h' hk hk']
 exact (hΔ.lap hk hr).add (h'.lap hΓ hC') (mul_nonneg hr hk.gain) (mul_nonneg hC' hΓ.gain)

theorem Held.bridge_diff (hm:0<p+q){r t s:ℝ}(h:Held d σ C F)(h':Held d σ C' F')(g:Held d σ D G)(g':Held d σ D' G')(hk:Wire d σ B Γ)(hk':Wire d σ B' Γ')(hΔ: Held d σ r (F-F'))(hΓ:Wire d σ t (Γ-Γ'))(hG:Held d σ s (G-G'))(hr:0≤r)(hC':0≤C')(hs:0≤s)(hD:0≤D)(hC:0≤C)(hD':0≤D'):
 Held d σ (r*B*D + C'*t*D + C'*B'*s) (Forms.bridge Γ F G - Forms.bridge Γ' F' G'):=by
 rw [bridge_compare hm h h' g g' hk hk' hC hC' hD hD']
 have hx:=hk.gain;have hw:=hk'.gain; have he:=hΓ.gain
 exact ((hΔ.bridge g hk hr hD).add (h'.bridge g hΓ hC' hD) (by positivity) (by positivity)).add (h'.bridge hG hk' hC' hs) (by positivity) (by positivity)
end YM.RG08.Forms
