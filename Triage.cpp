#include <iostream> //cout, cin
#include <fstream> //Чтение CSV-файла с пациентами
#include <sstream> //Разбор строк
#include <vector> // хранение листьев дерева, пациентов, весов
#include <cmath> //exp() в модели критичности, fabs() для порога (Модуль числа для типа double)
#include <random> 
#include <algorithm> //max_element, find, sort, swap, min 
#include <string>
#include <iomanip> //Форматирование вывода
#include <clocale>
#include <ctime>
#include <chrono>
#include <list> //для бенчмарка
#include <functional> //тип параметров в runBenchmark для передачи lambda-функций

using namespace std;
using namespace chrono;

struct Config {
    double THETA = 0.15;
    double DT = 5.0;
    bool auto_predict = true; //для проверки необходимости перестроения
    double MAX_INITIAL_WAIT_FRACTION = 0.3; //сколько уже потратил времени от безопасного
} config;

const double TARGET_TIME[] = { 120, 60, 15, 0 }; //максимальное безопасное время ожидания по уровню триажа [мин]
const double BASE_TREATMENT_TIME[] = { 10, 20, 30, 60 }; //ожидаемое время лечения по уровню [мин]
const double BASE_ALPHA[] = { 0.020, 0.013, 0.008, 0.002 }; //коэффициент скорости ухудшения по уровню [мин⁻¹]

random_device rd;
mt19937 rng(rd());

struct Timer {
    high_resolution_clock::time_point start;
    Timer() { start = high_resolution_clock::now(); }
    double elapsed_ms() {
        auto end = high_resolution_clock::now();
        return duration<double, milli>(end - start).count();
    }
};

struct Patient {
    int id;
    int level;
    double criticality;
    double remaining_time;
    double treatment_time;
    double alpha;
    double beta;
    double weight;
    double arrival_time;
    double wait_time;
    int age;
    double heart_rate;
    double systolic_bp;
    double oxygen_saturation;
    double temperature;
    int pain_level;
    int chronic_diseases;
    int prev_visits;
    string arrival_mode;

    void update_weight() { // w = 1 / (T_rem [мин] * T_treat [мин])
        if (remaining_time <= 0) weight = 0.0;
        else weight = 1.0 / (remaining_time * treatment_time);
    }

    void update_criticality_from_vitals() { //расчет критичности
        criticality = 0.0;
        if (heart_rate > 100 || heart_rate < 60) criticality += 15;
        if (systolic_bp > 140 || systolic_bp < 90) criticality += 15;
        if (oxygen_saturation < 92) criticality += 20;
        if (temperature > 38.5 || temperature < 36.0) criticality += 10;
        if (pain_level >= 8) criticality += 10;
        if (arrival_mode == "ambulance") criticality += 20;
        if (criticality > 100) criticality = 100;
    }

    void update_remaining_time_from_criticality() { //Пересчитывает оставшееся безопасное время пациента на основе его текущей критичности
        remaining_time = TARGET_TIME[level] * (1.0 - criticality / 100.0); //Оставшееся безопасное время = Максимальное безопасное время × (1 - критичность в долях)
        if (remaining_time < 0) remaining_time = 0;
        update_weight();
    }

    double predict_criticality(double dt) const { // dt в минутах, alpha в мин⁻¹
        if (fabs(alpha) < 1e-6) return criticality + beta * dt; //альфа ноль: S(t+dt) = S(t) + β·dt
        else return criticality * exp(alpha * dt) + (beta / alpha) * (exp(alpha * dt) - 1); //альфа не ноль S(t+dt) = S(t)·e^(α·dt) + (β/α)·(e^(α·dt) - 1)
    }

    double predict_weight(double dt) const {
        if (remaining_time <= 0) return 0.0; //если время вышло - пациент больше не приоритетен
        double S_pred = predict_criticality(dt); //предсказываем критичность через dt минут
        if (S_pred <= 0) return 0.0; //если критичность упала до нуля вес становится 0
        double T_rem_pred = remaining_time * (criticality / (S_pred + 0.01)); //прогноз ост времени
        if (T_rem_pred <= 0) return 0.0;
        double w = 1.0 / (T_rem_pred * treatment_time); //вычисление предск веса
        if (w > 1e6) w = 1e6;
        return w;
    }

    bool needs_rebuild(double dt) const {
        if (remaining_time <= 0) return false; //если время пациента вышло, то перестроение не нужно
        double w_pred = predict_weight(dt); //Предсказываем вес пациента через dt минут
        return fabs(w_pred - weight) > config.THETA * weight; //проверка насолько изменился вес
    }

    void update_wait_time(double delta_sec) { // delta — прошедшее время
        wait_time += delta_sec;
        remaining_time -= delta_sec;
        if (remaining_time < 0) remaining_time = 0;
        criticality = (remaining_time > 0) ? 100.0 * (1 - exp(-remaining_time / 3600.0)) : 0.0; //Пересчет критичности 
        if (criticality < 0) criticality = 0;
        if (criticality > 100) criticality = 100;
        update_weight();
    }

    void set_remaining_time(double minutes) {
        remaining_time = minutes * 60.0;
        if (remaining_time < 0) remaining_time = 0;
        criticality = (remaining_time > 0) ? 100.0 * (1 - exp(-remaining_time / 3600.0)) : 100.0;
        if (criticality < 0) criticality = 0;
        if (criticality > 100) criticality = 100;
        update_weight();
    }

    void worsen_random() {
        uniform_int_distribution<> param_dist(0, 5);
        int param = param_dist(rng);
        switch (param) {
        case 0: heart_rate *= (1.0 + uniform_real_distribution<>(0.1, 0.5)(rng)); break;
        case 1: systolic_bp *= (0.7 + uniform_real_distribution<>(0, 0.2)(rng)); break;
        case 2:
            oxygen_saturation -= uniform_real_distribution<>(3, 10)(rng);
            if (oxygen_saturation < 70) oxygen_saturation = 70;
            break;
        case 3: temperature += uniform_real_distribution<>(0.5, 2.0)(rng); break;
        case 4:
            pain_level += uniform_int_distribution<>(1, 3)(rng);
            if (pain_level > 10) pain_level = 10;
            break;
        case 5:
            chronic_diseases += 1;
            alpha *= 1.2;
            break;
        }
        update_criticality_from_vitals();
        update_remaining_time_from_criticality();
    }

    void init_from_csv(int new_id, int lvl,
        int a, double hr, double sbp, double spo2, double temp,
        int pain, int chronic, int prev, string mode) {
        id = new_id; level = lvl; arrival_time = 0;
        age = a; heart_rate = hr; systolic_bp = sbp;
        oxygen_saturation = spo2; temperature = temp;
        pain_level = pain; chronic_diseases = chronic;
        prev_visits = prev; arrival_mode = mode;
        remaining_time = TARGET_TIME[level];
        treatment_time = BASE_TREATMENT_TIME[level];
        alpha = BASE_ALPHA[level]; beta = 0.0;
        update_criticality_from_vitals();
        update_remaining_time_from_criticality();
        double max_wait = remaining_time * config.MAX_INITIAL_WAIT_FRACTION;
        uniform_real_distribution<> wait_dist(0, max_wait);
        wait_time = (remaining_time > 0 && max_wait > 0) ? wait_dist(rng) : 0;
        arrival_time = -wait_time;
        remaining_time -= wait_time;
        if (remaining_time < 0) remaining_time = 0;
        update_weight();
    }

    void print_info() const {
        cout << "ИНФОРМАЦИЯ О ПАЦИЕНТЕ id=" << id;
        cout << "Уровень триажа: " << level;
        cout << "\nВозраст: " << age << " лет";
        cout << "\nПульс: " << fixed << setprecision(0) << heart_rate << " уд/мин";
        cout << "\nДавление: " << systolic_bp << " мм рт.ст.";
        cout << "\nСатурация: " << oxygen_saturation << "%";
        cout << "\nТемпература: " << fixed << setprecision(1) << temperature << "°C";
        cout << "\nУровень боли: " << pain_level << "/10";
        cout << "\nХронические заболевания: " << chronic_diseases;
        cout << "\nПредыдущие обращения: " << prev_visits;
        cout << "\nСпособ поступления: " << arrival_mode;
        cout << "\nКритичность S(t): " << fixed << setprecision(2) << criticality;
        cout << "\nОставшееся безопасное время: " << remaining_time / 60.0 << " мин";
        cout << "\nОжидаемое время лечения: " << treatment_time / 60.0 << " мин";
        cout << "\nКоэффициент альфа: " << alpha;
        cout << "\nКоэффициент бета: " << beta;
        cout << "\nТекущий вес: " << fixed << setprecision(8) << weight;
        cout << "\nВремя ожидания: " << fixed << setprecision(1) << wait_time / 60.0 << " мин";
        if (remaining_time <= 0) cout << "\n[ВНИМАНИЕ] Безопасное время истекло!";
    }
};

struct HuffmanNode { //узел дерева
    int id;
    double weight;
    HuffmanNode* left;
    HuffmanNode* right;
    HuffmanNode* parent; //для быстрого обновления весов вверх
    bool is_leaf; //пациент или внутренний узел (для удаления или извлечения пациента)
    Patient* patient;

    HuffmanNode(int id, double w, Patient* p = nullptr);
    HuffmanNode(HuffmanNode* l, HuffmanNode* r);
};

//Для быстрого извлечения двух узлов с максимальным весом
class MaxHeap {
private:
    vector<pair<double, HuffmanNode*>> data;
    void siftUp(int i) {
        while (i > 0 && data[i].first > data[(i - 1) / 2].first) {
            swap(data[i], data[(i - 1) / 2]);
            i = (i - 1) / 2;
        }
    }
    void siftDown(int i) {
        int n = data.size();
        while (2 * i + 1 < n) {
            int left = 2 * i + 1, right = 2 * i + 2, largest = i;
            if (left < n && data[left].first > data[largest].first) largest = left;
            if (right < n && data[right].first > data[largest].first) largest = right;
            if (largest == i) break;
            swap(data[i], data[largest]);
            i = largest;
        }
    }
public:
    void push(double weight, HuffmanNode* node) {
        data.push_back({ weight, node });
        siftUp(data.size() - 1);
    }
    HuffmanNode* top() { return data[0].second; }
    void pop() {
        data[0] = data.back(); data.pop_back();
        if (!data.empty()) siftDown(0);
    }
    int size() const { return data.size(); }
    bool empty() const { return data.empty(); }
};

HuffmanNode::HuffmanNode(int id, double w, Patient* p)
    : id(id), weight(w), left(nullptr), right(nullptr), parent(nullptr),
    is_leaf(p != nullptr), patient(p) {
}

HuffmanNode::HuffmanNode(HuffmanNode* l, HuffmanNode* r)
    : id(-1), weight(l->weight + r->weight), left(l), right(r), parent(nullptr),
    is_leaf(false), patient(nullptr) {
    l->parent = this; r->parent = this;
}

// ИНВЕРСНОЕ ДЕРЕВО ХАФФМАНА
// аддитивное свойство — сравнивает суммарный прогнозируемый вес

class InverseHuffmanTree {
private:
    HuffmanNode* root;
    vector<HuffmanNode*> leaf_nodes; // все листья (пациенты)
    int patient_count;
    
    // для накопления изменений
    double W_initial;           // начальная сумма весов 
    bool has_initial;           // флаг, что начальная сумма сохранена
    double accumulated_time;    // накопленное время с последнего перестроения

    void deleteTree(HuffmanNode* node) {
        if (!node) return;
        deleteTree(node->left); deleteTree(node->right); delete node;
    }
    void updateParents(HuffmanNode* node, HuffmanNode* parent) {
        if (!node) return;
        node->parent = parent;
        updateParents(node->left, node); updateParents(node->right, node);
    }
    void updateAncestors(HuffmanNode* leaf) {
        if (!leaf->parent) return;
        HuffmanNode* current = leaf->parent;
        while (current) {
            double left_w = current->left ? current->left->weight : 0;
            double right_w = current->right ? current->right->weight : 0;
            current->weight = left_w + right_w;
            current = current->parent;
        }
    }
    HuffmanNode* buildTree(vector<double>& weights, vector<Patient*>& patients_list) {
        MaxHeap heap;
        leaf_nodes.clear();
        for (size_t i = 0; i < weights.size(); ++i) {
            HuffmanNode* leaf = new HuffmanNode((int)i, weights[i], patients_list[i]);
            heap.push(weights[i], leaf);
            leaf_nodes.push_back(leaf);
        }
        while (heap.size() > 1) {
            HuffmanNode* left = heap.top(); heap.pop();
            HuffmanNode* right = heap.top(); heap.pop();
            HuffmanNode* parent = new HuffmanNode(left, right);
            heap.push(parent->weight, parent);
        }
        HuffmanNode* new_root = heap.top();
        updateParents(new_root, nullptr);
        return new_root;
    }
    void updateAllWeights() {
        for (auto* leaf : leaf_nodes) {
            if (leaf->patient) {
                leaf->patient->update_weight();
                leaf->weight = leaf->patient->weight;
            }
        }
    }
    
    // Сброс начального состояния (вызывается после глобального перестроения)
    void resetInitialState() {
        W_initial = getRootWeight();
        accumulated_time = 0.0;
        has_initial = true;
    }

public:
    // Счётчики для анализа эффективности аддитивного свойства
    int ticks_total = 0;
    int rebuilds_global = 0;
    int rebuilds_skipped = 0;

    void printRebuildStats() const {
        cout << "\nСТАТИСТИКА ПЕРЕСТРОЕНИЙ ДЕРЕВА\n";
        cout << "  Всего тактов прогнозирования : " << ticks_total << "\n";
        cout << "  Глобальных перестроений      : " << rebuilds_global << "\n";
        cout << "  Пропущено (аддитивность O(1)): " << rebuilds_skipped << "\n";
        if (ticks_total > 0) {
            double pct = 100.0 * rebuilds_skipped / ticks_total;
            cout << "  Доля пропущенных перестроений: " << fixed << setprecision(1) << pct << "%\n";
            cout << "  Вывод: в " << rebuilds_skipped << " из " << ticks_total
                << " тактов проверка суммарного веса через корень (O(1))\n"
                << "  позволила избежать глобального перестроения O(n log n)\n";
        }
    }

    InverseHuffmanTree() : root(nullptr), patient_count(0), W_initial(0.0), has_initial(false), accumulated_time(0.0) {}
    ~InverseHuffmanTree() { deleteTree(root); }

    void insertPatient(Patient* patient) { //добавление пациента
        patient_count++;
        updateAllWeights();
        vector<double> weights; vector<Patient*> patients_list;
        for (auto* leaf : leaf_nodes) {
            if (leaf->patient) { weights.push_back(leaf->patient->weight); patients_list.push_back(leaf->patient); }
        }
        weights.push_back(patient->weight); patients_list.push_back(patient);
        HuffmanNode* new_root = buildTree(weights, patients_list);
        deleteTree(root); root = new_root;
        
        // После вставки нового пациента сбрасываем начальное состояние
        resetInitialState();
    }

    Patient* extractMax() { //извлечение пациента
        if (patient_count == 0) return nullptr;
        updateAllWeights();
        HuffmanNode* max_leaf = nullptr; double max_weight = -1.0;
        for (auto* leaf : leaf_nodes) {
            if (leaf->patient && leaf->weight > max_weight) { max_weight = leaf->weight; max_leaf = leaf; }
        }
        if (!max_leaf || max_leaf->weight == 0) return nullptr;
        Patient* result = max_leaf->patient;
        vector<double> weights; vector<Patient*> patients_list;
        for (auto* leaf : leaf_nodes) {
            if (leaf != max_leaf && leaf->patient) { weights.push_back(leaf->patient->weight); patients_list.push_back(leaf->patient); }
        }
        patient_count--;
        if (patient_count > 0) { HuffmanNode* new_root = buildTree(weights, patients_list); deleteTree(root); root = new_root; }
        else { deleteTree(root); root = nullptr; leaf_nodes.clear(); }
        
        // После извлечения пациента сбрасываем начальное состояние
        if (patient_count > 0) resetInitialState();
        else has_initial = false;
        
        return result;
    }

    void removePatient(int id) { //удаление 
        updateAllWeights();
        HuffmanNode* to_remove = nullptr;
        for (auto* leaf : leaf_nodes) { if (leaf->patient && leaf->patient->id == id) { to_remove = leaf; break; } }
        if (!to_remove) { cout << "Пациент с id=" << id << " не найден\n"; return; }
        vector<double> weights; vector<Patient*> patients_list;
        for (auto* leaf : leaf_nodes) {
            if (leaf != to_remove && leaf->patient) { weights.push_back(leaf->patient->weight); patients_list.push_back(leaf->patient); }
        }
        patient_count--;
        if (patient_count > 0) { HuffmanNode* new_root = buildTree(weights, patients_list); deleteTree(root); root = new_root; }
        else { deleteTree(root); root = nullptr; leaf_nodes.clear(); }
        cout << "Пациент id=" << id << " удалён из очереди\n";
        
        // После удаления пациента сбрасываем начальное состояние
        if (patient_count > 0) resetInitialState();
        else has_initial = false;
    }

    void setPatientRemainingTime(int patient_id, double minutes) { //ручное изменение времени пациента
        for (auto* leaf : leaf_nodes) {
            if (leaf->patient && leaf->patient->id == patient_id) {
                leaf->patient->set_remaining_time(minutes);
                leaf->weight = leaf->patient->weight;
                updateAncestors(leaf);
                rebuildTree();
                cout << "Пациенту id=" << patient_id << " установлено время "
                    << fixed << setprecision(0) << minutes << " мин\n";
                // После изменения времени сбрасываем начальное состояние
                resetInitialState();
                return;
            }
        }
        cout << "Пациент с id=" << patient_id << " не найден\n";
    }

    void rebuildTree() {
        if (leaf_nodes.empty()) return;
        updateAllWeights();
        vector<double> weights; vector<Patient*> patients_list;
        for (auto* leaf : leaf_nodes) {
            if (leaf->patient) { weights.push_back(leaf->patient->weight); patients_list.push_back(leaf->patient); }
        }
        HuffmanNode* new_root = buildTree(weights, patients_list);
        deleteTree(root); root = new_root;
        
        // После ручного перестроения сбрасываем начальное состояние
        resetInitialState();
    }

    // метод с накоплением изменений
    void applyPredictionAndRebuild(double dt) {
        if (leaf_nodes.empty()) return;
        
        // Если начальная сумма ещё не сохранена, сохраняем
        if (!has_initial) {
            W_initial = getRootWeight();
            has_initial = true;
            accumulated_time = 0.0;
        }
        
        // накопление времени с последнего перестроения
        accumulated_time += dt;
        
        // Текущая сумма весов
        double W_current = getRootWeight();
        if (W_current <= 0) return;
        
        // Прогноз суммы весов через накопленное время 
        double W_pred = 0.0;
        for (auto* leaf : leaf_nodes) {
            if (leaf->patient) W_pred += leaf->patient->predict_weight(accumulated_time);
        }
        
        // Изменение ОТ начального состояния
        double relative_change = fabs(W_pred - W_initial) / W_initial;
        
        ticks_total++;
        
        if (relative_change > config.THETA) {
            // Глобальное перестроение — накопилось достаточно изменений
            rebuilds_global++;
            
            // Обновляем веса до прогнозных значений
            for (auto* leaf : leaf_nodes) {
                if (leaf->patient && leaf->patient->remaining_time > 0) {
                    leaf->patient->weight = leaf->patient->predict_weight(accumulated_time);
                    leaf->weight = leaf->patient->weight;
                }
                else if (leaf->patient && leaf->patient->remaining_time <= 0) {
                    leaf->patient->weight = 0;
                    leaf->weight = 0;
                }
            }
            rebuildTree();
            
            // сброс начального состояния после перестроения
            resetInitialState();
        }
        else {
            rebuilds_skipped++;
            // Суммарный вес изменился незначительно — только локальные обновления
            bool any_local = false;
            for (auto* leaf : leaf_nodes) {
                if (!leaf->patient) continue;
                if (leaf->patient->remaining_time <= 0 && leaf->patient->weight != 0) {
                    leaf->patient->weight = 0;
                    leaf->weight = 0;
                    updateAncestors(leaf);
                    any_local = true;
                }
                
                else if (leaf->patient->needs_rebuild(dt)) {
                    leaf->patient->weight = leaf->patient->predict_weight(dt);
                    leaf->weight = leaf->patient->weight;
                    updateAncestors(leaf);
                    any_local = true;
                }
            }
            (void)any_local;
            // При пропуске перестроения НЕ сбрасываем W_initial и accumulated_time, изменения продолжают накапливаться дальше
        }
    }

    double getRootWeight() const { return root ? root->weight : 0.0; }
    int size() const { return patient_count; }
    bool empty() const { return patient_count == 0; }

    vector<Patient*> getAllPatients() { //для списка всех
        vector<Patient*> result;
        for (auto* leaf : leaf_nodes) { if (leaf->patient) result.push_back(leaf->patient); }
        return result;
    }

    Patient* findPatient(int id) { //найти по id
        for (auto* leaf : leaf_nodes) { if (leaf->patient && leaf->patient->id == id) return leaf->patient; }
        return nullptr;
    }
};
// СРАВНЕНИЕ СТРУКТУР ДАННЫХ
// Реализованы три структуры из главы 1.2 курсовой:
// 1. Несортированный список (O(1) вставка, O(n) извлечение)
// 2. Сортированный список  (O(n) вставка, O(1) извлечение)
// 3. Бинарная куча STL     (O(log n) обе операции)

// Несортированный список
struct UnsortedListQueue {
    vector<pair<double, int>> data; // (вес, id)
    void push(double w, int id) { data.push_back({ w, id }); }
    pair<double, int> extractMax() {
        auto it = max_element(data.begin(), data.end());
        auto result = *it; data.erase(it); return result;
    }
    int size() const { return data.size(); }
};

// Сортированный список (поддерживается в порядке убывания)
struct SortedListQueue {
    list<pair<double, int>> data;
    void push(double w, int id) {
        auto it = data.begin();
        while (it != data.end() && it->first > w) ++it;
        data.insert(it, { w, id });
    }
    pair<double, int> extractMax() {
        auto result = data.front(); data.pop_front(); return result;
    }
    int size() const { return data.size(); }
};

// Бинарная куча STL
struct BinaryHeapQueue {
    priority_queue<pair<double, int>> data;
    void push(double w, int id) { data.push({ w, id }); }
    pair<double, int> extractMax() { auto r = data.top(); data.pop(); return r; }
    int size() const { return data.size(); }
};

// Результат бенчмарка
struct BenchmarkResult {
    string name;
    double push_ms;
    double extract_ms;
    double total_ms;
    int n;
};
// Функция запуска сравнительного теста для заданного n
// Тестирует push и extractMax для всех трёх структур
BenchmarkResult runBenchmark(const string& name, int n,
    function<void(double, int)> push_fn,
    function<void()> extract_fn)
{
    BenchmarkResult res;
    res.name = name; res.n = n;

    // Генерация весов
    vector<double> weights(n);
    uniform_real_distribution<> w_dist(1e-6, 1.0);
    for (auto& w : weights) w = w_dist(rng);

    // Тест вставки
    Timer t1;
    for (int i = 0; i < n; ++i) push_fn(weights[i], i);
    res.push_ms = t1.elapsed_ms();

    // Тест извлечения
    Timer t2;
    for (int i = 0; i < n; ++i) extract_fn();
    res.extract_ms = t2.elapsed_ms();

    res.total_ms = res.push_ms + res.extract_ms;
    return res;
}

void runComparison(int n) {
    cout << "\nСРАВНЕНИЕ СТРУКТУР ДАННЫХ (n = " << n << " пациентов)\n";
    cout << left << setw(25) << "Структура"
        << right << setw(15) << "Вставка (мс)"
        << setw(15) << "Извлеч. (мс)"
        << setw(15) << "Итого (мс)" << "\n";

    vector<BenchmarkResult> results;

    // 1. Несортированный список
    {
        UnsortedListQueue q;
        auto res = runBenchmark("Несорт. список", n,
            [&](double w, int id) { q.push(w, id); },
            [&]() { q.extractMax(); });
        results.push_back(res);
    }

    // 2. Сортированный список
    {
        SortedListQueue q;
        auto res = runBenchmark("Сортир. список", n,
            [&](double w, int id) { q.push(w, id); },
            [&]() { q.extractMax(); });
        results.push_back(res);
    }

    // 3. Бинарная куча STL
    {
        BinaryHeapQueue q;
        auto res = runBenchmark("Бинарная куча", n,
            [&](double w, int id) { q.push(w, id); },
            [&]() { q.extractMax(); });
        results.push_back(res);
    }

    // 4. Инверсное дерево Хаффмана (только построение + извлечение)
    {
        // Генерируем минимальных пациентов для теста
        vector<Patient*> patients(n);
        for (int i = 0; i < n; ++i) {
            patients[i] = new Patient();
            patients[i]->id = i;
            patients[i]->remaining_time = 600 + i * 10;
            patients[i]->treatment_time = 1200;
            patients[i]->weight = 1.0 / (patients[i]->remaining_time * patients[i]->treatment_time);
        }

        BenchmarkResult res;
        res.name = "Инв. д. Хаффмана"; res.n = n;

        InverseHuffmanTree tree;
        Timer t1;
        for (int i = 0; i < n; ++i) tree.insertPatient(patients[i]);
        res.push_ms = t1.elapsed_ms();

        Timer t2;
        for (int i = 0; i < n; ++i) {
            Patient* p = tree.extractMax();
            if (!p) break;
        }
        res.extract_ms = t2.elapsed_ms();
        res.total_ms = res.push_ms + res.extract_ms;
        results.push_back(res);

        for (auto* p : patients) delete p;
    }

    for (auto& r : results) {
        cout << left << setw(25) << r.name
            << right << fixed << setprecision(3)
            << setw(15) << r.push_ms
            << setw(15) << r.extract_ms
            << setw(15) << r.total_ms << "\n";
    }
    cout << "\n";
}

struct CSVRecord {
    int level, age, pain_level, chronic_diseases, prev_visits;
    double heart_rate, systolic_bp, oxygen_saturation, temperature;
    string arrival_mode;
};

vector<CSVRecord> loadAllCSV(const string& filename) {
    vector<CSVRecord> records;
    ifstream file(filename);
    if (!file.is_open()) return records;
    string line;
    getline(file, line);
    while (getline(file, line)) {
        if (line.empty()) continue;
        stringstream ss(line); CSVRecord rec; string token;
        getline(ss, token, ','); rec.age = stoi(token);
        getline(ss, token, ','); rec.heart_rate = stod(token);
        getline(ss, token, ','); rec.systolic_bp = stod(token);
        getline(ss, token, ','); rec.oxygen_saturation = stod(token);
        getline(ss, token, ','); rec.temperature = stod(token);
        getline(ss, token, ','); rec.pain_level = stoi(token);
        getline(ss, token, ','); rec.chronic_diseases = stoi(token);
        getline(ss, token, ','); rec.prev_visits = stoi(token);
        getline(ss, token, ','); rec.arrival_mode = token;
        getline(ss, token, ','); rec.level = stoi(token);
        records.push_back(rec);
    }
    return records;
}

bool show_table = true;

void printQueueTable(const vector<Patient*>& patients) {
    if (!show_table) return;
    vector<Patient*> active, expired;
    for (auto* p : patients) { if (p->weight > 0) active.push_back(p); else expired.push_back(p); }
    sort(active.begin(), active.end(), [](Patient* a, Patient* b) { return a->weight > b->weight; });
    cout << "\n" << string(95, '-') << "\n";
    cout << "| " << setw(4) << "ID" << " | " << setw(5) << "УРОВ" << " | " << setw(14) << "ВЕС"
        << " | " << setw(10) << "ОЖИД(мин)" << " | " << setw(10) << "ОСТ(мин)"
        << " | " << setw(10) << "АЛЬФА" << " |" << endl;
    cout << string(95, '-') << "\n";
    for (auto* p : active) {
        cout << "| " << setw(4) << p->id << " | " << setw(5) << p->level
            << " | " << fixed << setw(14) << setprecision(8) << p->weight
            << " | " << fixed << setw(10) << setprecision(1) << p->wait_time / 60.0
            << " | " << setw(10) << setprecision(1) << p->remaining_time / 60.0
            << " | " << setw(10) << setprecision(3) << p->alpha << " |" << endl;
    }
    for (auto* p : expired) {
        cout << "| " << setw(4) << p->id << " | " << setw(5) << p->level
            << " | " << setw(14) << "0.00000000"
            << " | " << setw(10) << setprecision(1) << p->wait_time / 60.0
            << " | " << setw(10) << setprecision(1) << "0.0"
            << " | " << setw(10) << setprecision(3) << p->alpha << " | [ИСТЕКЛО]" << endl;
    }
    cout << string(95, '-') << "\n";
    cout << "Всего в очереди: " << patients.size()
        << " (активных: " << active.size() << ", истекших: " << expired.size() << ")" << endl;
}

class Simulator {
private:
    InverseHuffmanTree tree;
    vector<CSVRecord> all_csv_data;
    vector<Patient*> all_loaded_patients;
    int next_csv_index;
    double current_time;
    int next_patient_id;

    int getNextId() { return next_patient_id++; }

    void addPatientFromCSV(int csv_index) {
        if (csv_index >= (int)all_csv_data.size()) {
            cout << "Нет пациента с индексом " << csv_index << " в CSV (всего записей: " << all_csv_data.size() << ")\n";
            return;
        }
        const auto& rec = all_csv_data[csv_index];
        Patient* p = new Patient();
        p->init_from_csv(getNextId(), rec.level, rec.age, rec.heart_rate, rec.systolic_bp,
            rec.oxygen_saturation, rec.temperature, rec.pain_level,
            rec.chronic_diseases, rec.prev_visits, rec.arrival_mode);
        tree.insertPatient(p);
        all_loaded_patients.push_back(p);
        cout << "\n[ДОБАВЛЕН] Пациент id=" << p->id << ", уровень=" << p->level
            << ", вес=" << fixed << setprecision(8) << p->weight
            << ", возраст=" << p->age << " лет" << endl;
    }

    void autoPredict() {
        if (config.auto_predict && !tree.empty())
            tree.applyPredictionAndRebuild(config.DT);
    }

public:
    Simulator() : next_csv_index(0), current_time(0), next_patient_id(0) { srand(time(nullptr)); }
    ~Simulator() { for (auto* p : all_loaded_patients) delete p; }

    void autoLoadFirstPatients(const string& filename, int count = 50) {
        all_csv_data = loadAllCSV(filename);
        if (all_csv_data.empty()) {
            cout << "CSV-файл не найден или пуст. Генерация синтетических пациентов...\n";
            uniform_int_distribution<> level_dist(0, 3), age_dist(18, 90), pain_dist(0, 10), chronic_dist(0, 5), prev_dist(0, 5), mode_dist(0, 1);
            uniform_real_distribution<> hr_dist(60, 120), bp_dist(100, 160), spo2_dist(88, 100), temp_dist(36.0, 39.0);
            for (int i = 0; i < count; ++i) {
                CSVRecord rec;
                rec.level = level_dist(rng); rec.age = age_dist(rng);
                rec.heart_rate = hr_dist(rng); rec.systolic_bp = bp_dist(rng);
                rec.oxygen_saturation = spo2_dist(rng); rec.temperature = temp_dist(rng);
                rec.pain_level = pain_dist(rng); rec.chronic_diseases = chronic_dist(rng);
                rec.prev_visits = prev_dist(rng);
                rec.arrival_mode = (mode_dist(rng) == 0) ? "walk_in" : "ambulance";
                all_csv_data.push_back(rec);
            }
        }
        cout << "Загружено " << all_csv_data.size() << " записей. Добавляем первых "
            << min(count, (int)all_csv_data.size()) << " пациентов в очередь...\n";
        for (int i = 0; i < min(count, (int)all_csv_data.size()); ++i) addPatientFromCSV(i);
        next_csv_index = min(count, (int)all_csv_data.size());
    }

    void addNextFromCSV() {
        if (all_csv_data.empty()) { cout << "CSV не загружен\n"; return; }
        if (next_csv_index >= (int)all_csv_data.size()) { cout << "Все пациенты из CSV уже добавлены\n"; return; }
        addPatientFromCSV(next_csv_index++);
        autoPredict();
    }

    void addById(int csv_index) {
        if (all_csv_data.empty()) { cout << "CSV не загружен\n"; return; }
        if (csv_index < 0 || csv_index >= (int)all_csv_data.size()) {
            cout << "Индекс должен быть от 0 до " << all_csv_data.size() - 1 << endl; return;
        }
        addPatientFromCSV(csv_index);
        autoPredict();
    }

    void takePatient() {
        Patient* next = tree.extractMax();
        if (!next) { cout << "Очередь пуста или все пациенты с истекшим временем\n"; return; }
        double wait_time = current_time - next->arrival_time;
        cout << "\n[ПРИНЯТ] Пациент id=" << next->id << ", уровень=" << next->level
            << ", ожидал=" << fixed << setprecision(1) << wait_time / 60.0 << " мин"
            << ", вес=" << fixed << setprecision(8) << next->weight << endl;
        auto it = find(all_loaded_patients.begin(), all_loaded_patients.end(), next);
        if (it != all_loaded_patients.end()) all_loaded_patients.erase(it);
        delete next;
        autoPredict();
    }

    void removePatient(int id) {
        Patient* p = tree.findPatient(id);
        if (!p) { cout << "Пациент с id=" << id << " не найден в очереди\n"; return; }
        tree.removePatient(id);
        auto it = find(all_loaded_patients.begin(), all_loaded_patients.end(), p);
        if (it != all_loaded_patients.end()) all_loaded_patients.erase(it);
        delete p;
        autoPredict();
    }

    void setPatientRemainingTime(int id, double minutes) {
        tree.setPatientRemainingTime(id, minutes);
        autoPredict();
    }

    void worsenPatient(int id) {
        Patient* p = tree.findPatient(id);
        if (!p) { cout << "Пациент с id=" << id << " не найден в очереди\n"; return; }
        cout << "\n[УХУДШЕНИЕ] Пациент id=" << id << endl;
        p->worsen_random();
        cout << "  Новый вес: " << fixed << setprecision(8) << p->weight << endl;
        autoPredict();
    }

    void stepTime(double minutes) {
        if (minutes < 0) { cout << "Ошибка: время не может быть отрицательным\n"; return; }
        Timer t;

        current_time += minutes;
        auto patients = tree.getAllPatients();
        for (auto* p : patients) p->update_wait_time(minutes);
        cout << "\n[ВРЕМЯ] Прошло " << fixed << setprecision(1) << minutes << " мин";
        cout << " (время выполнения: " << fixed << setprecision(3) << t.elapsed_ms() << " мс)" << endl;
        autoPredict();
    }

    void showQueue() {
        Timer t;
        auto patients = tree.getAllPatients();
        printQueueTable(patients);
        cout << " (время выполнения: " << fixed << setprecision(3) << t.elapsed_ms() << " мс)" << endl;
    }

    void showPatientInfo(int id) {
        Timer t;
        Patient* p = tree.findPatient(id);
        if (!p) { cout << "Пациент с id=" << id << " не найден в очереди\n"; return; }
        p->print_info();
        cout << " (время выполнения: " << fixed << setprecision(3) << t.elapsed_ms() << " мс)" << endl;
    }

    void printHelp() {
        cout << "\nДОСТУПНЫЕ КОМАНДЫ:\n";
        cout << "  addnext                     - добавить следующего пациента из CSV\n";
        cout << "  add_id <индекс>             - добавить пациента из CSV по индексу\n";
        cout << "  take                        - принять следующего пациента\n";
        cout << "  remove <id>                 - удалить пациента из очереди\n";
        cout << "  set_rem <id> <мин>          - установить оставшееся безопасное время\n";
        cout << "  worsen <id>                 - ухудшение состояния пациента\n";
        cout << "  step <мин>                  - продвинуть время (в минутах)\n";
        cout << "  list                        - показать очередь\n";
        cout << "  info <id>                   - показать данные по пациенту\n";
        cout << "  benchmark                   - сравнение структур данных\n";
        cout << "  stats                       - статистика перестроений дерева\n";
        cout << "  help                        - показать эту справку\n";
        cout << "  exit                        - выход\n";
    }

    void runInteractive() {
        cout << "\nСимулятор запущен. Введите 'help' для списка команд.\n";
        string cmd;
        while (true) {
            cout << "> ";
            getline(cin, cmd);
            if (cmd.empty()) continue;
            stringstream ss(cmd); string action; ss >> action;

            if (action == "addnext") { Timer t; addNextFromCSV(); cout << " (время выполнения: " << fixed << setprecision(3) << t.elapsed_ms() << " мс)" << endl; }
            else if (action == "add_id") { int idx; if (ss >> idx) { Timer t; addById(idx); cout << " (время выполнения: " << fixed << setprecision(3) << t.elapsed_ms() << " мс)" << endl; } else cout << "Использование: add_id <индекс>\n"; }
            else if (action == "take") { Timer t; takePatient(); cout << " (время выполнения: " << fixed << setprecision(3) << t.elapsed_ms() << " мс)" << endl; }
            else if (action == "remove") { int id; if (ss >> id) { Timer t; removePatient(id); cout << " (время выполнения: " << fixed << setprecision(3) << t.elapsed_ms() << " мс)" << endl; } else cout << "Использование: remove <id>\n"; }
            else if (action == "set_rem") { int id; double minutes; if (ss >> id >> minutes) { Timer t; setPatientRemainingTime(id, minutes); cout << " (время выполнения: " << fixed << setprecision(3) << t.elapsed_ms() << " мс)" << endl; } else cout << "Использование: set_rem <id> <минуты>\n"; }
            else if (action == "worsen") { int id; if (ss >> id) { Timer t; worsenPatient(id); cout << " (время выполнения: " << fixed << setprecision(3) << t.elapsed_ms() << " мс)" << endl; } else cout << "Использование: worsen <id>\n"; }
            else if (action == "step") { double minutes; if (ss >> minutes) stepTime(minutes); else cout << "Использование: step <минуты>\n"; }
            else if (action == "list") showQueue();
            else if (action == "info") { int id; if (ss >> id) showPatientInfo(id); else cout << "Использование: info <id>\n"; }
            else if (action == "benchmark") {
                for (int n : {10, 50, 100}) runComparison(n);
            }
            else if (action == "stats") {
                tree.printRebuildStats();
            }
            else if (action == "help") printHelp();
            else if (action == "exit" || action == "quit") { cout << "Выход...\n"; break; }
            else cout << "Неизвестная команда. Введите 'help'\n";
        }
    }
};

int main() {
    setlocale(LC_ALL, "Russian");
    cout << "ДИНАМИЧЕСКОЕ ДЕРЕВО ХАФФМАНА\n";
    cout << "Симуляция очереди приёмного отделения\n";
    Simulator sim;
    sim.autoLoadFirstPatients("synthetic_medical_triage.csv", 50);
    sim.runInteractive();
    return 0;
}

