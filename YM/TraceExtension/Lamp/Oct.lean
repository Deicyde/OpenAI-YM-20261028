import YM.TraceExtension.Lamp.Code
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
variable {W:Type*}{g:W→Side}{H K:WickL G}{T:Reed G}{L:Filter W}(d i b a:Axis)(q j:G.ColorIndex)
section
variable (Q:Tendsto (fun w=> (g w).val) L atTop){Y:∀ w,Gal G (g w)}{F:∀ w,Peat G (g w)} (hp:Shine L T F)(h:knick F)(hs:G.Simple)(he:∀ w,Contours (F w))(hv:Fleam L Y K)(hV:∀ w,Cloaked (Y w))(hK: CodeM (g:=g) (fun _=>0) (fun w=>Y w ∘ input G (g w)) 1)
include Q hp h hs he hv hV hK
lemma buzz (x:Dish) : Tendsto (fun w=> ((pitchf (g w):ℂ)⁻¹)^ (3:ℕ) * cue d i q b (rill (F w) (Y w) ∘ input G (g w)) x) L (𝓝 (∑ a:Loc G 1, song d i b q K T a x)):=by
    let t:= pitchf ∘ g; let A:= (ra d x.1); let B:= reab d b x; let j:= mood G i q
    have hz(a:Loc G 1)(p:Cover):=culled Q a j p h he hs (hp.tracks _ _)
    have ht(a:Loc G 1)(p q:Cover):=wick_span Q hK hV hs hv a j p q
    have hx:= tendsto_finsetSum (s:=univ) fun a (_:a∈univ) => ((hz a B).mul (ht a A B)).add ((hz a A).mul (ht a B A))
    refine hx.congr' (Eventually.of_forall fun w=>?_)
    dsimp only; rw [cue,clipP,rill_wave hs (he w).coat (hV w),shark_ro (he w), shark_ro (he w)]; simp_rw [dotProduct_sum,dotProduct_smul]; rw [mul_add, sum_add_distrib]; apply congr_arg₂ (·+·)
    all_goals rw [Finset.mul_sum]; apply sum_congr rfl; intro p _; unfold tann; simp only [smul_eq_mul,A,B,j]; ring
lemma ardor : Tendsto (fun w=> lux d i q b (rill (F w) (Y w) ∘ input G (g w))) L (𝓝 (∑ a:Loc G 1,Deb (song d i b q K T a))):=by
    rw [← map_sum]; unfold lux; let P(w)(x:Dish):= ((pitchf (g w):ℂ)⁻¹)^ (3:ℕ)*cue d i q b (rill (F w) (Y w) ∘ input G (g w)) x; let Z:= (∑ a:Loc G 1,song d i b q K T a)
    have hp(x:Dish): Tendsto (fun w=> P w x) L (𝓝 (Z x)):=by unfold Z;rw[Finset.sum_apply];exact buzz d i b q Q hp h hs he hv hV hK x
    have hv(x:ℤ): Tendsto (fun w=> FlopZ fun y=> P w (x,y)) L (𝓝 (FlopZ fun y=> Z (x,y))):=by
       simp_rw[flopi]; exact ((((hp (x,1)).sub (hp (x,-1))).const_mul _|>.sub ((hp (x,2)).sub (hp (x,-2)))).const_mul _)
    change Tendsto (fun w=>Complex.I * PanZ fun x=>FlopZ fun y=> P w (x,y)) L (𝓝 (Complex.I * PanZ fun x=> FlopZ fun y=> Z (x,y)))
    simp_rw[pani]; exact (((((hv 1).sub ((hv 0).const_mul _)).add (hv (-1))).const_mul _).const_mul _)
end
lemma high_filter {X:Type*}{f:W→X}{L:Filter W}{S:Filter X}(h:∀ v:Ultrafilter W, ↑v ≤ L → Tendsto f v S): Tendsto f L S:=by
    intro y hy; by_contra he
    have hp:(L⊓𝓟 ({x| ¬ f x∈ y})).NeBot:= frequently_iff_neBot.mp (show ∃ᶠ x in L, ¬ f x∈y from by
       rw[frequently_iff_neBot];
       apply Filter.frequently_iff_neBot.mp; rw[Filter.Frequently]; simp only [not_not]; exact he)
    obtain ⟨v,hv⟩:=Ultrafilter.exists_le (L⊓𝓟 {x| ¬ f x∈y})
    have hc := (h v (hv.trans inf_le_left)) hy
    have hz:∀ᶠ x in (↑v:Filter W), ¬ f x∈y:= le_principal_iff.mp (hv.trans inf_le_right); exact (hz.and (show ∀ᶠ x in (↑v:Filter W), f x∈y from hc)).exists.elim fun _ hf=> hf.1 hf.2
-- orientation theta per pair
abbrev Panels (G:Gauge)(f:Side):=Axis→Maze G f
abbrev fata (F:Panels G f):ℂ:=∑ b:Axis,lux d i q b (F b)
-- polarization linear selector
def xup(F:Panels G f):ℂ:=∑ d:Axis,∑ i:Axis,(if d=i then 0 else fata d i q F)
section
variable {Y:∀ w,Axis→Gal G (g w)}{F:∀ w,Peat G (g w)}
    (Q:Tendsto (fun w=> (g w).val) L atTop)(h:knick F)(hs:G.Simple)(he:∀ w,Contours (F w))(hp:∀ w a,Cloaked (Y w a))(ht:∀ a,CodeM (g:=g) (fun _=>0) (fun w=>Y w a∘ input G (g w)) 1)
include Q h hs he hp ht
lemma arcPay : Tendsto (fun w=> xup q (fun a=> rill (F w) (Y w a) ∘ input G (g w))) L (𝓝 0):=by
    apply high_filter; intro v hv
    have hQ:= Q.mono_left hv; obtain ⟨T,hT⟩:= shine v h; choose K hK using (fun a=> flamed v (ht a) (fun w=> hp w a)); have ha(a): Kelly (K a) := know hQ (fun w=>hp w a) hs (ht a) (hK a)
    have ht':= shines hQ h hT he hs
    have hx(d i): Tendsto (fun w=> if d=i then 0 else ∑ b:Axis,lux d i q b (rill (F w) (Y w b) ∘ input G (g w))) (↑v:Filter W) (𝓝 (if d=i then 0 else ∑ b:Axis,∑ a:Loc G 1,Deb (song d i b q (K b) T a))):=by
       by_cases h0:d=i
       · simp only[h0,↓reduceIte]; exact tendsto_const_nhds
       simp only[h0,↓reduceIte]; exact tendsto_finsetSum _ fun b _=>ardor d i b q hQ hT h hs he (hK b) (fun w=>hp w b) (ht b)
    have hl:= tendsto_finsetSum _ (fun d (_: d∈univ)=> tendsto_finsetSum _ (fun i (_:i∈univ)=> hx d i))
    suffices H: (∑ d:Axis,∑ i:Axis,(if d=i then 0 else ∑ b:Axis,∑ a:Loc G 1,Deb (song d i b q (K b) T a)))=0 from by rw [H] at hl; exact hl
    let R(d i j:Axis)(c:G.ColorIndex): ℂ:= ∑ b:Axis,Deb (song d i b q (K b) T (coord j,c))
    let V(d i:Axis)(c:G.ColorIndex):= if d=i then (0:ℂ) else ∑ b:Axis,∑ j:Axis,Deb (song d i b q (K b) T (coord j,c))
    have hs: ∀ d i:Axis,(if d=i then (0:ℂ) else ∑ b:Axis,∑ a:Loc G 1,Deb (song d i b q (K b) T a))=∑ c,V d i c :=by
       intro d i; by_cases hd:d=i; simp [V,hd]
       simp only[V,hd,↓reduceIte,Fintype.sum_prod_type]; rw [sum_comm (f:=fun c b=> ∑ a:Axis,Deb (song d i b q (K b) T (coord a,c)))]; refine sum_congr rfl fun b _=>?_ ;rw[← Equiv.sum_comp axisEquiv,sum_comm]; rfl
    simp_rw [hs]
    have hu(d): (∑ i,∑ c,V d i c)=∑ c,∑ i, V d i c:=sum_comm
    simp_rw [hu];rw [sum_comm]; exact sum_eq_zero fun i _=> turn_tank q i ht' ha
end
end YM.Trace.Lamp
