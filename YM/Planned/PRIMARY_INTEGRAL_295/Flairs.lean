import YM.Planned.PRIMARY_INTEGRAL_295.Castles
import YM.Planned.PRIMARY_INTEGRAL_295.Hoods
import YM.Planned.PRIMARY_INTEGRAL_295.Ranches
/-!
# Rotor.T Full dark entry colors

Use full actual Gauge. Q-phase uniform requires oriented k tags.
Covariance assumes Branches & etc, no changing supplied representative
or history.Up.P. Curvature global analytic not needed even (but paid at
contact). Cut zero large distances. E tests separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Flairs
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Hives Candles Barges Hoods
open Next.Fluctuations Work.E03
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G:Gauge} {c f n : Side} {S:StepData c f}
variable (K:Core G S) (V:Config G c)(z: Site c→G.El)
-- hinge colors on rows.
def bend (z:G.El) : G.Color ≃L[ℝ] G.Color := LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofLinear (G.adjoint z) (G.adjoint z⁻¹)
   (LinearMap.ext fun x=> by show G.adjoint z (G.adjoint z⁻¹ x)=x; rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one])
   (LinearMap.ext fun x=> by show G.adjoint z⁻¹ (G.adjoint z x)=x; rw [← G.adjoint_mul,inv_mul_cancel,G.adjoint_one]))

private lemma atom (z:Site f→G.El)(U V:Config G f)(x:Site f)(s:Slot):
    kink s (Lattice.gauge z U) (Lattice.gauge z V) x= G.adjoint (z x) (kink s U V x):=by
   unfold kink; simp only [expandAt_gauge,travel_gauge,face_gauge,G.curvature_conjugate]
   -- stops near on aligned cover
   simp only [Slot.offset,map_zero,zero_add]
   rw [G.adjoint_mul,G.adjoint_mul, ← G.adjoint_mul (z _ )⁻¹ _,inv_mul_cancel,G.adjoint_one]
lemma stucco (z:Site f→G.El)(U V:Config G f)(i:Twin f):
    (if i.2 then ∑' j,K.mbTerm (Lattice.gauge z U) (Lattice.gauge z V) i.1 j else shoot K.tube.high (Lattice.gauge z V) i.1)=
     G.adjoint (z i.1.1) (if i.2 then ∑' j,K.mbTerm U V i.1 j else shoot K.tube.high V i.1):=by
   split <;> rename_i h
   · let F:=bend (z i.1.1); change _=F (∑' j,K.mbTerm U V i.1 j); rw [F.map_tsum]
     apply tsum_congr; intro j; dsimp only [mbTerm]; split
     · rw [map_smul,atom]; rfl
     rw [map_zero]
   rw [shoot,shoot,face_gauge,G.curvature_conjugate,map_smul]
lemma lotto (z:Site n→G.El) (P:PathData G)(A:Clip)(U:Config G n)(i:Twin n)(R d:ℕ):plotted P A R d (Lattice.gauge z U) i=
     G.adjoint (z i.1.1) (plotted P A R d U i):=by
   unfold plotted; split
   · let F:= bend (z i.1.1); change (∑' j,_)=F (∑' j,_); rw [F.map_tsum]
     apply tsum_congr; intro j; unfold shortenTerm; split
     · rw [PathData.ellTerms,PathData.ellTerms,map_smul]; exact congr_arg _ (atom z U U i.1.1 (P.row i.1.2 j).2)
     rw [map_zero]
   rw [shoot,shoot,face_gauge,G.curvature_conjugate,map_smul]

-- M.K table uses have crossing endpoint TRUE.T. aggregated even tsum.B.
private lemma act_n (g:Site n→G.El) (U:Config G n)(i:Site n)(w:Walk)(r:ℝ)(u:G.Color):
    rated (Lattice.gauge g U) i w r (G.adjoint (g (stop i w)) u)=G.adjoint (g i) (rated U i w r u):=by
    change r • G.adjoint (travel (Lattice.gauge g U) i w) _ = G.adjoint _ (r • G.adjoint _ _)
    rw [map_smul,travel_gauge,G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul (g _)⁻¹ _, inv_mul_cancel,G.adjoint_one]
private lemma levy (T T':Cover→Pay G) (a b : G.El)(h:∀ i v,T' i (G.adjoint a v)=G.adjoint b (T i v))(v:G.Color):
     (∑' i,T' i) (G.adjoint a v)=G.adjoint b ((∑' i,T i) v):=by
   let f:G.Color ≃L[ℝ] G.Color:=bend a; let g:= bend b
   let F:Pay G ≃L[ℝ] Pay G:= f.arrowCongr g
   have hf(i:Cover): T' i=F (T i):=by
      ext1 x; obtain ⟨v,rfl⟩:= f.surjective x; change T' i (G.adjoint a v)=g (T i (f.symm (f v)))
      rw [f.symm_apply_apply,h]; rfl
   change _=g ((∑' i,T i) v); simp_rw [hf]; rw [← F.map_tsum]; change g ((∑' i,T i) (f.symm (f v)))=_; rw [f.symm_apply_apply]

lemma lever (x:Twin f) (y:Twin c) (v:G.Color):
     K.tube.Φ K.R (Lattice.gauge z V) x y (G.adjoint (z y.1.1) v)=G.adjoint (flatten (S:=S) z (x.1.1,0)) (K.tube.Φ K.R V x y v) :=by -- 0 Axis? ok
   apply levy; intro i v; dsimp only [Pressure.casted]; split<;> rename_i h
   · rw [← copied S.ratio S.patch.odd_side]
     let x':= (mesh x).1; let w:=route (lift (S.ratio.residue (mesh x).1)) (S.patch.L.val • i) 1
     have he:y.1.1=S.ratio.parent (stop x' w):= by rw [show stop x' w=_ from casted_endpoint S x' i,S.ratio.embed_parent]; exact h.2
     conv_lhs => right; rw [he]
     exact act_n (z∘S.ratio.parent) _ _ _ _ _
   change _=G.adjoint _ 0; rw [map_zero]; rfl
lemma pitch (x:Bond c) (y:Twin c)(v:G.Color):
    K.tube.Φ' K.R (Lattice.gauge z V) x y (G.adjoint (z y.1.1) v)=G.adjoint (z x.1) (K.tube.Φ' K.R V x y v):=by
   apply levy; intro i v; unfold Pressure.priced; split <;> rename_i h
   · have he : y.1.1=stop (pole x).1 (route 0 i 1):=by rw [show y.1.1= _ from h.2]; simpa using (Work.E03.stop_route (pole x).1 0 i).symm
     conv_lhs => right; rw [he]
     exact act_n ..
   change _=G.adjoint _ 0; rw [map_zero]; rfl
-- now orientations.
lemma strings (d:Drops c f)(hb:S.patch.Branches S.kernel G):
     garth K d (Lattice.gauge z V)=G.adjoint (z (shade S d)) (garth K d V) ∧
     ∀ a, logs K d (Lattice.gauge z V) (harvest.burn (flatten (S:=S) z) a) = G.adjoint (z (shade S d)) (logs K d V a):=by
   let s:=d.1; let U:=pull s 0 V; let p:=push_gauge z s; let r:=S.ratio; let A:=owl K s V; let F:=Lattice.gauge z V; let D:=harvest.burn (flatten (S:=S) z)
   have he:owl K s (Lattice.gauge z V) 0= Lattice.gauge (p ∘ r.parent) (A 0):=by simpa only [map_zero] using glows K V z s 0 -- check args order
   have hh:corn K s (Lattice.gauge z V) 0=Lattice.gauge p (corn K s V 0):=by simpa only [map_zero] using bubble K V z s 0 hb
   have ht(i:Twin c): K.tube.Xn K.R (pull s 0 (Lattice.gauge z V)) i=G.adjoint (p i.1.1) (K.tube.Xn K.R U i):=by rw [pulls]; exact lotto ..
   obtain ⟨s',i|i⟩:= d
   · have hz : z (shade S (s,i |> Sum.inl))=p (r.parent i.1.1):=by unfold p push_gauge r shade; simp [affine,S.ratio.parent_signed S.patch.odd_side]
     constructor
     · change K.tube.Xf K.R (owl K s (Lattice.gauge z V) 0) i -_=G.adjoint (z (shade S (s,.inl i))) (_-_)
       rw [he,hz,map_sub]; apply congr_arg₂ _ (lotto ..) ?_
       change Pressure.zip (K.tube.Φ K.R (pull s 0 (Lattice.gauge z V))) (K.tube.Xn K.R (pull s 0 (Lattice.gauge z V))) i= _
       unfold Pressure.zip; rw [map_sum]
       apply Finset.sum_congr rfl; intro j _; rw [ht j,pulls]; exact lever ..
     intro a; change crease K s F i (D a)=G.adjoint (z (shade S (s,.inl i))) (crease K s V i a)
     unfold crease F D; rw [hz,he,glows]; exact stucco ..
   let q:=p i.1; let e:=p (i.1+step i.2)
   have hy : p i.1=z (shade S (s,.inr i)):= rfl
   constructor
   · change Pressure.Tube.Z S (corn K s (Lattice.gauge z V) 0) _ i -_= G.adjoint _ (Pressure.Tube.Z S _ U i-_); rw [map_sub]
     apply congr_arg₂ _
     · rw [hh,pulls]; unfold Pressure.Tube.Z Lattice.gauge; rw [map_smul]
       apply congr_arg; change G.curvature (q*U i*e⁻¹*(q*_ *e⁻¹)⁻¹)= G.adjoint q (G.curvature _)
       rw [show q*U i*e⁻¹*(q*(corn K s V 0 i)*e⁻¹)⁻¹=q * (U i*_)*q⁻¹ from ?_]; exact G.curvature_conjugate .. -- stuck _
       group; rfl
     unfold Pressure.zip; rw [map_sum]; apply Finset.sum_congr rfl; intro j _; change K.tube.Φ' K.R (pull s 0 F) _ j (K.tube.Xn K.R (pull s 0 F) j)= _
     unfold F; rw [ht j, pulls]; exact pitch ..
   intro a; change gruel K s F i (D a)=G.adjoint q (gruel K s V i a)
   unfold gruel F D; rw [bubble _ _ _ _ _ hb,hh,map_smul]; unfold Lattice.gauge; apply congr_arg
   change G.curvature (q* corn K s V a i * e⁻¹ * (q*corn K s V 0 i * e⁻¹)⁻¹)= G.adjoint _ _
   rw [← G.curvature_conjugate]; apply congr_arg; group

end YM.Planned.PrimaryIntegral295.Flairs
