import YM.RG08.Bands.Sutra
/-!
# Discrepancy exact thermal tree-source recurrence
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I α :Type} [Fintype α]{u:List I}{a:I→ℕ}{F V:Screed ℝ α}{S:Canticle α}{U:I→ Screed ℝ α}{K:Row α α}{p:Option Side}{t k n e:ℕ}{m c:Side}
def birth (p:Option Side)(K:Row α α)(S:Canticle α)(X:I→Screed ℝ α)(u:List I): HeatS α:= murmur p K S (castF X u)-castM (fun i=>murmur p K S (X i)) u
lemma drew_z : castM (fun i=>murmur p K S (U i)) u 0=castF U u := by induction u with | nil=> change upstart _ 0=spine_one α; rw [upstart,if_pos rfl] | cons b u ih=> change borne (murmur _ _ _ _) (castM _ u) 0= gust (U b) (castF U u); rw [borne_z,ih,show murmur p K S (U b) 0=U b from funext fun i=>funext fun v=> by rw [murmur]]
lemma birth_zero : birth p K S U u 0=0:= by unfold birth; rw [Pi.sub_apply,drew_z,show murmur p K S (castF U u) 0=castF U u from funext fun i=>funext fun v=>by rw [murmur],sub_self]
lemma dressing (h:Sails t V)(he:Whole K)(hs:Gets S): Reels t (murmur p K S V):= fun i=> swung fun j=> ⟨quiet_tidily he (fun i j=>hs.2 i j|>.1) h.tide p i j, fun k hk=> not_ne_iff.mp (mt (murmur_degree he (fun i j=>hs.2 i j|>.1) hs.1 h.tide h.budget) (fun H=> by omega))⟩
lemma towboat (h:∀ i∈u,Sails (a i) (U i))(hp:Whole K)(hx: Gets S): Reels (loadᵣ a u) (birth p K S U u):= Reels.less (dressing (cast_s h) hp hx) (cast_r (fun i hi=>dressing (p:=p) (h i hi) hp hx))
lemma payB (h:∀ i∈u,Sails (a i) (U i))(hp:Whole K)(hx:Gets S): Reels (loadᵣ a u) (pumpP p K S (birth p K S U u)+pullG p K (fun i=>murmur p K S (U i)) u):= by
   have ht:= towboat (p:=p) h hp hx; exact Reels.more ((reeling_peels (p:=p) ht hp).more (reeling_choir hp hx ht)) (zapH (fun i hi=> dressing (p:=p) (h i hi) hp hx) hp)
lemma swingD (h:∀ i∈u,Sails (a i) (U i))(hp:Whole K)(hx:Gets S)(z:Site c)(he:(K.acts c)ᵀ=K.acts c):
   let v := birth (some c) K S U u; let i:=loadᵣ a u
   glee i z (ticks v)=glee i z (pumpP (some c) K S v+pullG (some c) K (fun i=>murmur (some c) K S (U i)) u) := by
   intro v i; let y(b:I):=murmur (some c) K S (U b); let W:= Beats K S c; let A:=murmur (some c) K S (castF U u); let P:=castM y u; have ht:= towboat (p:=some c) h hp hx
   have hh b hb:= dressing (p:=some c) (h b hb) hp hx; have hA:= dressing (p:=some c) (cast_s h) hp hx
   have hz (U:Screed ℝ α) n (h:Sails n U) : countT (glee n z (murmur (some c) K S U))=coda (K.acts c) W (glee n z (murmur (some c) K S U)):= (pendants z hp (fun i j=> hx.2 i j|>.1) hx.1 h.tide h.budget).2.2
   have hP:= cast_r hh; have hM:Reels i v:= ht
   rw [tallyD hM,glee_m (τ:=i) (V:=pullG (some c) K y u) (U:=pumpP (some c) K S v) (show Reels _ _ from Reels.more (reeling_peels (p:=some c) hM hp) (reeling_choir hp hx hM)) (zapH hh hp)]; unfold pumpP; rw [glee_m (τ:=i) (reeling_peels hM hp) (reeling_choir hp hx hM),peelsD hM hp,choirD hM hp hx]
   change countT (glee (loadᵣ a u) z v)= coda (K.acts c) W (glee (loadᵣ a u) z v)+ _
   unfold v birth; rw [glee_sub hA hP, drum_c (glee_sway hA z) (glee_sway hP z),show ∀ f g: Op (Co c α), countT (f-g) = countT f-countT g from fun f g=> funext fun i=>funext fun j=> smul_sub .., hz _ _ (cast_s h), pulsed hh hp z he W (fun i hi=>hz _ _ (h i hi))]; abel
-- True cover no period-transmission premise
lemma burnout (hx:∀ i∈u,Sails (a i) (U i))(hp:Whole K)(he: Gets S)(hk:∀ c,(K.acts c)ᵀ=K.acts c) :
    let F:=birth none K S U u; ticks F= pumpP none K S F+pullG none K (fun i=>murmur none K S (U i)) u:= by
  let p (i:ℕ):Side := ⟨i+1,Nat.succ_pos _⟩; have ht:Tendsto (fun i=>(p i).val) atTop atTop:= tendsto_add_atTop_nat _
  have hA (V:Screed ℝ α) n (h:Sails n V): Tips (fun i=> murmur (some (p i)) K S V) (murmur none K S V):= fun i j k=>Hurled.furs (U:=fun _=>V) p (fun i k=>Hurled.fixed (h.tide i k|>.pens)) he hp ht
  have hs : Tips (fun i=> birth (some (p i)) K S U u) (birth none K S U u):= tips_sub (F:=fun i=>murmur (some (p i)) K S (castF U u)) (Q:=fun i=>_) (hA _ _ (cast_s hx)) (tips_z (fun i hi=>hA _ _ (hx i hi)))
  intro F
  refine relic (m:=p) (F:=fun i=> ticks (birth (some (p i)) K S U u)) (W:=fun i=> pumpP (some (p i)) K S (birth (some (p i)) K S U u)+pullG (some (p i)) K (fun v=>murmur (some (p i)) K S (U v)) u) (fun i j k=> Hurled.scale (hs (i+1) j k) _) (reels_tick (towboat hx hp he)) (tips_more (F:=fun i=>_) (Q:=fun i=>_) (tips_peel hp he ht hs) (tips_p (f:=fun v i=>murmur (some (p i)) K S (U v)) (fun i hi=> hA _ _ (hx i hi)) hp ht)) (payB hx hp he) (fun _=> reels_tick (towboat hx hp he)) (fun _=>payB hx hp he) ht (fun i=> swingD hx hp he (0:Site (p i)) (hk _))
end YM.RG08.Bands
