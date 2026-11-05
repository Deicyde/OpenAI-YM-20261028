import YM.TraceExtension.Fen.Shy
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}(R:Rep G n){I:Type}(b:I→Barley) {k:ℕ}{σ a A C D E p q v u w:ℝ}
variable {Y Y':Gal G n}{F F':Peat G n}
lemma peat_main (h:R.path.Bounds R.clip σ A C):Cleric (Main R):=by
    refine ⟨?_,fun _ _ _ _ _ V W _ _ _ _ _=>Eventually.of_forall fun t=> Work.F05.mainTerm_gauge h _ _⟩
    exact Work.F02.mainTerm_contDiffAt (A:=input G n) h (Army.powL (v:=id) contDiffAt_id)
lemma peat_p (h:R.path.Bounds R.clip σ A C) (L:Finset I):Cleric (piste R b L):=by
    have hp (s:Seat n)(i:I):seatP R b (s,i)∈ clergy G n:=by
        change Cleric _; exact ⟨lick R b (s,i) _ _ (Army.powL (v:=id) contDiffAt_id), fun _ _ _ _ _ _ _ _ _ _ _ _=> Eventually.of_forall fun x=>ferInv R _ _ h _ _⟩
    exact (clergy _ _).sum_mem (t:=univ) (f:=fun s=> ∑ i∈ L,seatP R b (s,i)) (fun s _=> (clergy _ _).sum_mem fun i _=>hp s i)
lemma out_zero (h:Cleric F)(hp:G.Simple)(e:Lines G n 1):outD F e 1=0:=by simp only [outD,mul_one,show (fun y=> F (input G n y))=F ∘ input G n from rfl,dyed_hold h hp,ContinuousLinearMap.zero_apply]
lemma suppY {o:Site n}(hY:Y∈rains G n)(hp:Estate o (bottom Y) v (fun _=>C))(hY':Y'∈rains G n)(ht:Estate o (bottom (Y-Y')) v (fun _=>D)): Estate o (bottom Y') v (fun _=>C+D):=by
    have he:Y'=Y-(Y-Y'):=by abel
    let W:= follic (G:=G) (f:=n)
    have hf:bottom Y'=bottom Y+(-1:ℝ) • bottom (Y-Y'):=by rw[neg_one_smul,← sub_eq_add_neg]; exact (congr_arg W he).trans (map_sub ..)
    have hx:= (rain_read ((rains G n).sub_mem hY hY')).2.2.1; let M:= bottom (Y-Y')
    refine ⟨fun i hi hk=>?_⟩; rw [hf]; let F1:=bottom Y; let F2:= (-1:ℝ) • M
    rw [show Perfect.leaf (F1+F2) 0 i= Perfect.leaf F1 0 i+Perfect.leaf F2 0 i from ?_]; rotate_left
    · unfold Perfect.leaf; rw[iteratedFDeriv_add_apply (f:=F1) (g:=F2) ((rain_read hY).2.2.1.of_le le_top) ((hx.const_smul (c:=(-1:ℝ))).of_le le_top)]; rfl
    refine le_trans (cost_add ..) (add_le_add (hp.values i hi hk) ?_); change cost (landW _) _ _ _ (Perfect.leaf ((-1:ℝ) • M) _ _) ≤ _
    rw [cell_fee _ _ _ _ _ hx,abs_neg,abs_one,one_mul]; exact ht.values _ hi hk
lemma duck (h:R.path.Bounds R.clip σ A C)(L: Finset GreenA)(r:ℕ)(hG:G.Simple){o:Site n}(hy:Y∈rains G n)(hy':Y'∈rains G n)(he:Estate o (bottom (Y-Y')) v (fun _=>p))(hY:Estate o (bottom Y) v (fun _=>q))(hv:0<v)(hp:0 ≤ p)(hq:0≤ q)(hu:0≤ u)(hw:0≤ w)
 (ht: ∀ e:Lines G n 1, Allows 4 (outD (Main R) e ∘ input G n) 0 u) (hP:∀ e:Lines G n 1,Allows 4 (outD (Main R-ski R legF L r) e ∘ input G n) 0 w) : Allows 4 ((aroma R.clip R.path Y - rill (ski R legF L r) Y') ∘ input G n) 0 (vocation G v p u+vocation G v (q+p) w):=by
    let V:=ski R legF L r; let F:= Main R; let H:= aroma (f:=n) R.clip R.path
    have hz:= peat_main R h
    have hyF:=receives (Y:=Y-Y') ((rains G n).sub_mem hy hy') he hv hp hu (fun i=>⟨out_zero hz hG i,ht i⟩)
    have ha: Cleric (F-V):= (clergy _ _).sub_mem (x:=F) (y:=V) hz (peat_p R legF h _)
    have hp:=hyF.add (receives hy' (suppY hy hY hy' he) hv (add_nonneg hq hp) hw (fun i=>⟨out_zero ha hG i,hP i⟩))
    refine hp.germ (Eventually.of_forall (fun x=>?_))
    let U:=input G n x; change beamG F U (Y U-Y' U)+beamG (F-V) U (Y' U)= H Y U-_
    have hx:∀ v:Link G n, beamG (F-V) U v=beamG F U v-beamG V U v:=by
       intro v; unfold beamG; rw [show bal _ _=bal U F-bal U V from rfl,fderiv_sub]; rfl; exact (lightsA R U h).differentiableAt (by simp); exact slopeD R legF _ U
    rw [hx,map_sub]; change _=beamG F U (Y U) - beamG V U (Y' U); ring
lemma shedU {X:Sway G n}{Z:Dart G n}(b:Axis)(r:ℕ)(o:Site n)(L:Finset GreenA)
  {Amt:ℝ}{r':ℕ} (he:Viz Z R.clip R.path σ (fun _=>A) (fun _=>q) p) (hp:Bond (boom Z.J b) (boom X b) k r' v Amt C D)(ha:0<v)(hc:0≤C)(hs:0<σ)(hq:0 ≤q)(hx:Y∈ rains G n)
 (h:Allows 4 ((aroma R.clip R.path (Z.Y b o) - rill (ski R legF L r) Y) ∘ input G n) 0 E):
    Allows 4 ((boom X b o - rill (ski R legF L r) Y) ∘ input G n) 0 (q*gable G (σ/5) 4 + C*gable G (v/5) 4 + E):=by
    let F:= boom Z.J b o; let R':= aroma R.clip R.path (Z.Y b o); let P:= rill (ski R legF L r) Y; let V:=Z.E b o
    obtain ⟨hw,hZ,hR⟩ := he.sound.fin b o
    have hg: (∑ i:Axis,elm i (Z.J i b)) o= F:= Finset.sum_apply ..
    change Cleric ((∑ i:Axis,elm i (Z.J i b)) o-V) at hw; rw[hg] at hw
    change braid ((((∑ i:Axis,elm i (Z.J i b)) o) - V) ∘ _) (R' ∘ input G n) 0 4 at hR; rw[hg] at hR
    let S:=(F-R')∘ input G n; have hv:V∈loom G n:= he.sound.plum ..
    have hp':=para o (pea_loom hv (he.E ..) hq hs.le) (show 0<σ/5 by positivity) hq
    have hu: Allows 4 S 0 (q*gable G (σ/5) 4):=by
       have hF:S=V∘input G n + ((F-V)∘ input G n - R' ∘ input G n):=by funext x; unfold S; simp only[Function.comp_apply,Pi.add_apply,Pi.sub_apply];abel
       rw[hF]; change Cleric R' at hZ; let A(x):=((F-V)∘input G n - R' ∘ input G n) x; have he':ContDiffAt ℝ ω A 0:=hw.dye.sub hZ.dye
       refine ⟨hp'.analytic.add he',fun k hi=>?_⟩
       have hh:iteratedFDeriv ℝ k A 0=0:=by unfold A; rw[iteratedFDeriv_sub_apply (hw.dye.of_le le_top) (hZ.dye.of_le le_top),hR k hi,sub_self]
       rw [iteratedFDeriv_add_apply (hp'.analytic.of_le le_top) (he'.of_le le_top),hh,add_zero]; exact hp'.norm_le k hi
    have hb:= hp.lid o; have h':= (para o (pea_loom hb.cloth hb.pay hc ha.le) (show 0<v/5 by positivity) hc).smul (-1); rw[abs_neg,abs_one, one_mul] at h'
    apply ((hu.add h').add h).germ (Eventually.of_forall fun x=> ?_); change S x+(-1:ℝ) • (F _-boom X b o _)+ (R' _- P _) = boom X b o _-P _; simp only[S,Function.comp_apply, Pi.sub_apply, neg_one_smul]; ring
end YM.Trace.Fen
