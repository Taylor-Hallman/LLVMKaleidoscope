#pragma once

#include <cassert>
#include <unordered_map>

template<typename T, typename U, 
    typename THash = std::hash<T>, typename UHash = std::hash<U>,
    typename TEqual = std::equal_to<T>, typename UEqual = std::equal_to<U>>
class Bimap {
    std::unordered_map<T, U, THash, TEqual> m1;
    std::unordered_map<U, T, UHash, UEqual> m2;

    void eraseInternal(const T& first, const U& second) {
        m1.erase(first);
        m2.erase(second);
    }

    bool insertInternal(const T& first, const U& second) {
        if (!m1.insert(std::make_pair(first, second)).second)
            return false;
        bool bl = m2.insert(std::make_pair(second, first)).second;
        assert(!m1.empty() && !m2.empty());
        return bl;
    }

public:    
    bool insert(const T& first, const U& second) {
        return insertInternal(first, second);
    }

    bool insert(const U& first, const T& second) {
        return insertInternal(second, first);
    }

    void erase(const T& key) {
        eraseInternal(key, m1.at(key));
    }

    void erase(const U& key) {
        eraseInternal(m2.at(key), key);
    }

    void update(const T& key, const U& newValue) {
        erase(key);
        insert(key, newValue);
    }

    void update(const U& key, const T& newValue) {
        erase(key);
        insert(key, newValue);
    }

    int size() const {
        return m1.size();
    }

    const U& at(const T& key) const {
        return m1.at(key);
    }

    const T& at(const U& key) const {
        return m2.at(key);
    }
    bool contains(const T& key) {
        return m1.contains(key);
    }

    bool contains(const U& key) {
        return m2.contains(key);
    }

    bool empty() {
        return m1.empty();
    }
};
