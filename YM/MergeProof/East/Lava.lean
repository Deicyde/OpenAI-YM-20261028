import YM.MergeProof.East.Crust

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.East
open Function Filter RG Labels Source Source.Drops Thirst Baler Lattice Wilson MeasureTheory Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise MvPolynomial Configuration
open Further.CorrectedLift.Compass
open scoped InnerProductSpace BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{b J k i N p d:ℕ} {C:Family G} {t a g δ:ℝ} {V U :Config G n}
-- Instead require chord of REGISTERED inside V.A.Rotate
lemma metra (s:Signed)(P:Turn b)(hv:∀ i,G.chord (V i) ≤ δ) (he:0≤δ)(hp: G.chord (registered b V 0 (swing s P)) ≤ t)(H:2*(b+1)<n.val)(ht:0≤t):
   ‖G.curvature (registered b (pull s 0 V) 0 P) - wind s P.val.2 • G.curvature (registered b V 0 (swing s P))‖ ≤
    2*(2*G.colorScale*((4*(b:ℝ)+2)*δ))*t := by
    rw [show G.curvature (registered b _ _ _)= (crown P).atSite (pull s 0 V) 0 from inner _ P,Further.CorrectedLift.Compass.pocket]
    let z:=bend G s (crown P);let V0:=crown (swing s P); let M:Face (Per n):=(wrap n (swing s P).val.1 + 0, (swing s P).val.2)
    let v:=G.curvature (faceValue V M)
    have h' : G.chord (faceValue V M) ≤ t := by rw [registering b V H] at hp; unfold spine at hp; rw [Lattice.face_gauge,G.chord_conj] at hp; exact hp
    let e:=(4*(b:ℝ)+2)*δ
    have hL (W : Walk) (hx:W.length ≤ 4*b+2): ‖G.adjoint (travel V 0 W) v-v‖ ≤ (2*G.colorScale*e)*t:=by
       let u:=travel V 0 W; apply (Fluctuations.adjoint_norm_sub u v).trans; apply mul_le_mul _ ((G.curvature_norm _).trans h') (norm_nonneg _) (by unfold e; have h:=G.colorScale_pos; positivity); apply mul_le_mul_of_nonneg_left _ (by have h:=G.colorScale_pos; positivity); refine (Fluctuations.travel_chord V W 0 δ hv).trans (mul_le_mul_of_nonneg_right ?_ he); exact_mod_cast hx
    have h1: V0.walk.length ≤ 4*b:= by change (Spindle.paths _).length≤_; rw [Spindle.lengths]; exact bounded (faceOrigin _)
    have h2: z.walk.length≤4*b+2:= (lesser G s (crown P)).trans ((Nat.add_le_add_right (by change (Spindle.paths _).length ≤ _; rw [Spindle.lengths]; exact bounded (faceOrigin P)) 2))
    rw [show G.curvature (registered b V 0 (swing s P))=V0.atSite V 0 from inner ..]; change ‖wind s P.val.2 • z.atSite V 0-wind s P.val.2 • V0.atSite V 0‖ ≤ _
    rw [← smul_sub,norm_smul,norm_wind,one_mul,Work.F03.atSite_path,Work.F03.atSite_path]
    rw [show Work.F03.slotFace z (0:Site n)=M from congr_arg (fun p : Face ℤ=>((wrap n p.1+0,p.2):Face (Per n))) (bent G s P),show Work.F03.slotFace V0 (0:Site n)=M from by unfold Work.F03.slotFace; rw [show V0.offset = _ from (show V0.offset=(swing s P).val.1 from stops ..)]; rfl]
    let a:= G.adjoint (travel V (0:Site n) z.walk) v;let b':= G.adjoint (travel V (0:Site n) V0.walk) v
    change ‖a-b'‖ ≤ _; rw [show a-b'= (a-v)-(b'-v) by abel]; exact (norm_sub_le ..).trans ((add_le_add (hL _ h2) (hL _ (h1.trans (by omega)))).trans_eq (by dsimp only [e];ring))

-- pull chord agrees Hold.He
lemma earn_ping (s:Signed)(he:0<t)(δ:ℝ)(h:2*(b+1)<n.val) (hv:∀ i,G.chord (V i) ≤ δ)(hδ:0≤δ)(ho: Healthy t (Spindle.patch b 0) U)
   (hV:Agrees (Spindle.patch b (0:Site n)) V (spine U 0)) (hg:0<g)(A:poly (slotC G b))(hA:totalDegree A ≤ J):
   ‖signet 0 g A (pull s 0 V) - signet 0 g (exchange (pivot s) A) V‖ ≤ coin A*(J*(max 1 (t/g))^J*(g⁻¹*(2*(2*G.colorScale*((4*(b:ℝ)+2)*δ))*t))):=by
    have hu : Healthy t (Spindle.patch b 0) (spine U 0):= by unfold Healthy spine; rw [gauge_flags]; exact ho
    have heq := s_locale s 0 (Spindle.patch b 0) V (spine U 0) (by rw [Spindle.patch,swath_here]; exact hV)
    have hx(p:Turn b): G.chord (registered b (pull s 0 V) 0 p) ≤ t:=by
       rw [show registered b (pull s 0 V) 0 p=registered b (pull s 0 (spine U 0)) 0 p from reads_face b 0 p _ _ heq]; exact chords _ _ t ((s_healthy ..).mpr (by rw [Spindle.patch,swath_here]; exact hu)) h p
    have hy(p:Turn b): G.chord (registered b V 0 p) ≤ t:=by rw [show registered b V 0 p=registered b (spine U 0) 0 p from reads_face b 0 p _ _ hV]; exact chords b (spine U 0) t hu h p
    let M:=max 1 (t/g);let L:= fun p:Turn b=>curl b (pull s 0 V) g 0 p; let K:=fun p:Turn b=>wind s p.val.2 • curl b V g 0 (swing s p)
    have h1(p): ‖L p‖≤ M:=by unfold L Spindle.curl; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg).le]; dsimp only [M]; rw [div_eq_inv_mul]; exact (mul_le_mul_of_nonneg_left ((G.curvature_norm ..).trans (hx p)) (inv_pos.mpr hg).le).trans (le_max_right ..)
    have h2(p): ‖K p‖≤ M:=by unfold K Spindle.curl; rw [norm_smul,norm_wind,one_mul,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg).le]; dsimp only [M]; rw [div_eq_inv_mul]; exact (mul_le_mul_of_nonneg_left ((G.curvature_norm ..).trans (hy _)) (inv_pos.mpr hg).le).trans (le_max_right ..)
    have h3(p): ‖L p-K p‖ ≤ g⁻¹*(2*(2*G.colorScale*((4*(b:ℝ)+2)*δ))*t):=by
       unfold L K Spindle.curl; rw [smul_comm (wind s _) g⁻¹,← smul_sub,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg).le];exact mul_le_mul_of_nonneg_left (metra s p hv hδ (hy _) h he.le) (inv_pos.mpr hg).le
    have ht(q:G.Color)(i:G.ColorIndex): |q i| ≤ ‖q‖:=by
       rw [show q i = ⟪EuclideanSpace.basisFun G.ColorIndex ℝ i,q⟫_ℝ by simp only [EuclideanSpace.basisFun_inner]] -- arg order
       exact (abs_real_inner_le_norm _ _).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])
    unfold signet; rw [phased]
    exact amove A J hA M (le_max_left ..) _ _ (fun i=>(ht (L i.1) i.2).trans (h1 i.1)) (fun i=>(ht (K i.1) i.2).trans (h2 i.1)) _ (by have h:=G.colorScale_pos;positivity) (fun i=>(ht (L i.1-K i.1) i.2).trans (h3 i.1))
end YM.Next.Rank.East
