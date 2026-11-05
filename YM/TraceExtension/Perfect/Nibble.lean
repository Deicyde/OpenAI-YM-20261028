import YM.TraceExtension.Perfect.Corals
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free Asymptotics RowGrade
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {W Y X:Type} [Fintype Y] [Fintype X] {α B C S:ℝ} {t:ℕ}
lemma two_p (P:Type) [NormedAddCommGroup P][NormedSpace ℝ P] (a:X→P)(b:Y→ P)(u:X→ℝ)(v:Y→ℝ)(T : P [×2]→L[ℝ] ℝ):
    T ![∑ i, u i • a i,∑ j,v j • b j]= ∑ i,∑ j, u i*v j*T ![a i,b j]:=by
 choose A F he hp using link_v T; let Q:=∑ j,v j • b j; rw [show T ![∑ i, u i • a i,Q]=_ from hp Q _,map_sum]; simp_rw [map_smul,smul_eq_mul]; apply Finset.sum_congr rfl; intro i _
 change u i * F Q (a i) = _; simp_rw [← hp Q, he (a i),mul_assoc]; unfold Q; rw [map_sum,mul_sum];simp_rw [map_smul,smul_eq_mul]

variable {F:Filter W} {G:Gauge} {c f: W→Side}
variable (R:∀ w, pairA G (c w)→ℕ)(Q:∀ w,(Acr G (f w)) [×2]→L[ℝ] ℝ)
    (P:∀ w,pairA G (f w) → pairA G (c w)→ℝ)(U:∀ w,pairA G (f w) → pairA G (c w)→ℝ)
    (p:∀ w,X→Acr G (f w))(q:∀ w, Y→ Acr G (f w))(L:∀ w,X→ pairA G (c w)→ℝ)(l:∀ w,Y→ pairA G (c w)→ℝ)
lemma table_lotto (h:∀ w i,(fun j=> P w j i)=∑ a,L w a i • p w a)(he:∀ w i,(fun j=> U w j i)=∑ a,l w a i • q w a)
    (hp:0≤α)(hc:0≤ C)(hB:0 ≤ B)(hy:∀ᶠ w in F,∀ i, sh (R w) α t 0 (L w i) ≤ C)(hx:∀ᶠ w in F,∀ i, sh (R w) α t 0 (l w i)≤B)
    (hv:∀ i j, Tendsto (fun w=> Q w ![p w i,q w j]) F (𝓝 0)): Tendsto (fun w=> cost (R w) α t 0 (bisect (P w) (U w) (Q w))) F (𝓝 0):=by
 let s w i j:= Q w ![p w i,q w j]; let f w i j (v:Fin 2→pairA G (c w)) := (L w i (v 0)* l w j (v 1)) * s w i j
 have hh w: bisect (P w) (U w) (Q w)= fun v=> ∑ i,∑ j,f w i j v :=by
    funext v; rw [name_bisect,h,he]; exact two_p _ _ _ _ _ _
 let T (w:W) :ℝ:=∑ i,∑ j,C*B*‖s w i j‖
 have ht:Tendsto T F (𝓝 0):=by apply opt0 _ (fun i=> opt0 _ (fun j=> ?_)); simpa only [norm_zero,mul_zero] using! ((hv i j).norm.const_mul (C*B))
 refine squeeze_zero' (Eventually.of_forall (fun i=> cost_nn ..)) ?_ ht
 filter_upwards [hy,hx] with w hu hy; rw [hh]; refine (cost_sum (F:=fun i v=> ∑ j, f w i j v) _ _ _ _).trans (sum_le_sum (s:=univ) (fun i _=> ?_))
 exact (cost_sum (F:=fun j v=> f w i j v) _ _ _ _).trans (sum_le_sum (fun j _=>le_trans (le_of_eq (cost_smul _ _ _ _ (fun v:Fin 2→ pairA G (c w)=>L w i (v 0)*l w j (v 1)) (s w i j))) (mul_le_mul_of_nonneg_right ((coat _ _ t 0 _ _ hp le_rfl).trans (mul_le_mul (hu i) (hy j) (sh_nn ..) hc)) (norm_nonneg _))))

lemma earth_acts (n:W→Side)(A:∀ w,Acr G (n w)→ ℝ)(p:∀ w,Site (n w))(h:Stoke F p A 0 4)(z v: Ore G): Tendsto (fun w=> iteratedFDeriv ℝ 2 (A w) 0 ![meshOre z (p w),meshOre v (p w)]) F (𝓝 0):= h.taste _ _ (by exact (show 2+2≤4 by decide))
lemma wind_acts (n:W→Side)(A:∀ w,Acr G (n w)→ℝ)(p:∀ w,Site (n w))(h:Stoke F p A 0 5)(z: Ore G)(u:Bar G) (t:Bool):
  Tendsto (fun w=>let a:=meshOre z (p w);let b:=meshBar u (p w);iteratedFDeriv ℝ 2 (A w) 0 (if t then ![a,b] else ![b,a])) F (𝓝 0):=by
 let M w:=iteratedFDeriv ℝ 2 (A w) 0; let Z w:= meshOre z (p w)
 obtain ⟨y,hV,hW⟩ : ∃ y:∀ w,Acr G (n w)→ₗ[ℝ] ℝ,(∀ w v, (M w) (if t then ![Z w,v] else ![v,Z w])=y w v)∧ ∀ j:Tit G, Tendsto (fun w=> y w (ballad j (p w))) F (𝓝 0) :=by
    choose V K H he using fun w=> link_v (M w) (Z w)
    have hP(i:Tit G): ScoreG i+2 ≤ 5:= (by have hh:= chapel i.1; unfold ScoreG;omega)
    split_ifs; · exact ⟨V,H,fun j=> (h.taste ((.foot z.2,z.1):Tit G) j (show 2+ScoreG j≤ 5 from Nat.add_comm .. ▸ hP j)).congr (fun i=>H i _)⟩
    exact ⟨K,he,fun j=> (h.taste j ((.foot z.2,z.1):Tit G) (hP j)).congr (fun i=>he i _)⟩
 rcases u with ⟨v,a,b⟩|v
 · change Tendsto (fun w=>M w (if t then ![Z w,meshBar (Sum.inl (v,a,b)) (p w)] else ![meshBar (Sum.inl (v,a,b)) (p w),Z w])) _ _; simp_rw [hV]
   simp_rw [prism_foot,map_sub,map_smul,smul_eq_mul]; simp_rw [map_sub,map_smul,smul_eq_mul]
   simpa only [mul_zero,sub_zero] using! ((((hW (.paw a b,v)).sub ((hW (.paw a a,v)).const_mul _)|>.sub ((hW (.paw b b,v)).const_mul _)).const_mul _).sub ((hW (.foot a,v)).const_mul _))
 refine (hW (.watch,v)).congr fun i=>?_ ; exact (hV i _).symm
end YM.Trace.Perfect
