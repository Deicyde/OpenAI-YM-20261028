import YM.RG08.Forms.Dial

/-!
# Coefficient comparisons at one set of scales (fees polynomial in input prices W and
smoothly, multiplicatively small in input changes δ). Set δ=0 and take the same data twice
for absolute uses; no ratio/log hypotheses on W or identities of inputs at this stage.
-/
noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I:Type}{p q n:ℕ}

structure Cot (d:Ground I) (σ δ W : ℝ)(F F':Flake n I):Prop where
 gain : 0≤W
 near : Held d σ W F
 far  : Held d σ W F'
 compare : Held d σ (W*δ) (F-F')

structure WireCot (d:Ground I)(σ δ W:ℝ)(Γ Γ':Forms.Line I):Prop where
 near : Wire d σ W Γ
 far : Wire d σ W Γ'
 compare : Wire d σ (W*δ) (Γ-Γ')

variable {Γ Γ':Forms.Line I}{F F' G G':Flake n I}{d:Ground I}{σ τ δ P Q B:ℝ}

lemma Cot.mono (h:Cot d σ δ P F F')(hs:τ≤σ)(hp:P≤Q)(hd:0≤δ):Cot d τ δ Q F F':= ⟨h.gain.trans hp,h.near.mono hs hp (fun _=>le_rfl),h.far.mono hs hp (fun _=>le_rfl),h.compare.mono hs (by gcongr) (fun _=>le_rfl)⟩
lemma Cot.add (h:Cot d σ δ P F F')(h':Cot d σ δ Q G G')(hd:0≤δ):Cot d σ δ (P+Q) (F+G) (F'+G'):=by
 refine ⟨add_nonneg h.gain h'.gain,h.near.add h'.near h.gain h'.gain,h.far.add h'.far h.gain h'.gain,?_⟩
 rw [add_sub_add_comm,add_mul];exact h.compare.add h'.compare (mul_nonneg h.gain hd) (mul_nonneg h'.gain hd)
lemma Cot.sum {J:Type}(S:Finset J)(F G:J→Flake n I)(B:J→ℝ)(h:∀ i∈S,Cot d σ δ (B i) (F i) (G i))(hd:0≤δ):Cot d σ δ (S.sum B) (S.sum F) (S.sum G):=by
 refine ⟨Finset.sum_nonneg fun i hi=>(h i hi).gain,Held.sum S _ _ (fun i hi=>(h i hi).gain) fun i hi=>(h i hi).near,Held.sum S _ _ (fun i hi=>(h i hi).gain) fun i hi=>(h i hi).far,?_⟩
 rw [←Finset.sum_sub_distrib,Finset.sum_mul];exact Held.sum S _ _ (fun i hi=>mul_nonneg (h i hi).gain hd) fun i hi=>(h i hi).compare
lemma Cot.zero (P:ℝ)(h:0≤P):Cot d σ δ P (0:Flake n I) 0:=by constructor <;> simp [h,zero_held]
lemma Cot.scalar (P:ℝ)(h:0≤P){F G:Flake 0 I}:Cot d σ δ P F G:=by
 have he (F:Flake 0 I)(p:ℝ):Held d σ p F:=ensign.mpr fun i=>Fin.elim0 i
 exact ⟨h,he _ _,he _ _,he _ _⟩
lemma Cot.smul (h:Cot d σ δ P F F')(a:ℝ): Cot d σ δ (|a| * P) (a • F) (a • F') := by
 refine ⟨mul_nonneg (abs_nonneg _) h.gain,h.near.smul a,h.far.smul a,?_⟩
 rw [←smul_sub,mul_assoc];exact h.compare.smul a
lemma Cot.shift (h:Cot d σ δ P F F'){a b:ℝ}(hab:|a-b| ≤Q*δ)(ha:|a|≤Q)(hb:|b|≤Q)(hd:0≤δ):Cot d σ δ (2*(Q*P)) (a • F) (b • F'):=by
 have hQ := (abs_nonneg a).trans ha
 have hP:=h.gain
 refine ⟨by positivity,(h.near.smul a).mono le_rfl (by nlinarith [mul_nonneg (sub_nonneg.mpr ha) hP]) (fun _=>le_rfl),(h.far.smul b).mono le_rfl (by nlinarith [mul_nonneg (sub_nonneg.mpr hb) hP]) (fun _=>le_rfl),?_⟩
 rw [show a • F - b • F'= (a-b) • F+a • (F-F')+(b-a) • (F-F') from by module] -- simplify to b
 rw [add_assoc,←add_smul,show a+(b-a)=b from by ring]
 exact ((h.near.smul (a-b)).add (h.compare.smul b) (by positivity) (by positivity)).mono le_rfl (by nlinarith [mul_nonneg (sub_nonneg.mpr hab) hP,mul_nonneg (sub_nonneg.mpr hb) (mul_nonneg hP hd)]) (fun _=>le_rfl)
lemma Cot.lap' {F F':Flake (n+2) I} (h:Cot d σ δ P F F')(hk:WireCot d σ δ B Γ Γ')(hd:0≤δ):Cot d σ δ (2*P*B) (lap Γ F) (lap Γ' F'):=by
 rcases eq_or_ne n 0 with hn|hn
 · subst hn; exact Cot.scalar _ (by have he:=h.gain;have hx:=hk.near.gain;positivity)
 have he:=h.gain;have hx:=hk.near.gain
 refine ⟨by positivity,(h.near.lap hk.near he).mono le_rfl (by nlinarith) (fun _=>le_rfl),(h.far.lap hk.far he).mono le_rfl (by nlinarith) (fun _=>le_rfl),?_⟩
 convert Held.lap_diff (Nat.pos_of_ne_zero hn) h.near h.far hk.near hk.far h.compare hk.compare (by positivity) he using 1;ring
lemma Cot.bridge' {F F':Flake (p+1) I}{G G':Flake (q+1) I} (h:Cot d σ δ P F F')(h':Cot d σ δ Q G G')(hk:WireCot d σ δ B Γ Γ')(hd:0≤δ): Cot d σ δ (3*(P*B*Q)) (bridge Γ F G) (bridge Γ' F' G'):=by
 have he:=h.gain;have hx:=h'.gain;have hB:=hk.near.gain
 rcases eq_or_ne (p+q) 0 with hh|hh
 · obtain ⟨rfl,rfl⟩:p=0∧q=0:=by omega
   exact Cot.scalar _ (by positivity)
 refine ⟨by positivity,(h.near.bridge h'.near hk.near he hx).mono le_rfl (by nlinarith [mul_nonneg (mul_nonneg he hB) hx]) (fun _=>le_rfl),(h.far.bridge h'.far hk.far he hx).mono le_rfl (by nlinarith [mul_nonneg (mul_nonneg he hB) hx]) (fun _=>le_rfl),?_⟩
 convert Held.bridge_diff (Nat.pos_of_ne_zero hh) h.near h.far h'.near h'.far hk.near hk.far h.compare hk.compare h'.compare (by positivity) he (by positivity) hx he hx using 1;ring
end YM.RG08.Forms
